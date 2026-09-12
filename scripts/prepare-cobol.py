#!/usr/bin/env python3
"""Give nonrecursive helpers a secondary public ENTRY for GnuCOBOL 3.2.

The runtime walks the entire module stack on every primary-entry call. Making
all helpers RECURSIVE avoids that walk but allocates module/frame/decimal state
on every call. A secondary ENTRY skips the walk and reuses nonrecursive module
state. LOCAL-STORAGE remains initialized per call. Recursive programs are
unchanged. Debug builds compile the original sources to retain recursion checks.
Only COBOL entry declarations change; procedure bodies are copied verbatim.
"""
import argparse
import hashlib
from pathlib import Path
import re


def prepare(source):
    blocks = source.split('identification division.')
    for i in range(1, len(blocks)):
        block = blocks[i]
        header = re.search(r'program-id\. ([\w-]+)( recursive)?\.', block)
        if header is None:
            raise ValueError('Missing program-id')
        if header[2]:
            continue
        name = header[1]
        private = name[:21] + '-' + hashlib.sha256(name.encode()).hexdigest()[:8]
        procedure = re.search(r'procedure division( using[^.]+)?\.', block)
        if procedure is None or re.search(r'^entry\b', block, re.M):
            raise ValueError(f'Unsupported procedure declaration: {name}')
        block = block[:procedure.end()] + '\nentry "' + name + '"' + (procedure[1] or '') + '.' + block[procedure.end():]
        block = block.replace(f'program-id. {name}.', f'program-id. {private}.', 1)
        block = block.replace(f'end program {name}.', f'end program {private}.', 1)
        blocks[i] = block
    return 'identification division.'.join(blocks)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.write_text(prepare(args.source.read_text()))
