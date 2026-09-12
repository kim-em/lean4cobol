01 tx-vector based.
   02 tx-entry occurs 1 to 67108864 depending on tx-count.
      03 tx-key binary-long unsigned.
      03 tx-value binary-long unsigned.
01 tx-cache based.
   02 tx-slot occurs 1 to 67108864 depending on tx-cache-cap.
      03 tx-expr binary-long unsigned.
      03 tx-depth binary-long unsigned.
      03 tx-result binary-long unsigned.
