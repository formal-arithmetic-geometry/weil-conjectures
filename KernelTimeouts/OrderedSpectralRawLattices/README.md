# OrderedSpectralRawLattices

Historical Before/After reproduction for `f4946fdb6b6`. The files include the
one current API compatibility rename documented in `CLASSIFICATION.md`.

Run from the master build tree:

```text
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1200 nice -n 10 lake env lean \
  -DElab.async=false -Ddebug.skipKernelTC=false KernelTimeouts/OrderedSpectralRawLattices/Before.lean
```

Use `After.lean` for the fixed form and `probes/Before.lean` or
`probes/After.lean` for the copied probe sources.

