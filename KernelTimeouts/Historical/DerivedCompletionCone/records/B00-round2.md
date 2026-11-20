# B00 round two

The fresh source `probes/round2/B-inline.lean` declares the inline cone with `:= sorry`.
On v4.33.1 it reaches Lean's deterministic kernel timeout at 118.66 s and exits 1.
The process peak RSS was 13,826,340 kB. This is a direct fresh B1.1 timeout; the
first-pass `>600 s` value is historical, not re-measured.
