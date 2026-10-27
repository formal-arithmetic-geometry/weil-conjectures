# Local compiler fallback repair (K1, 2026-10-26)

The active launcher compiler at `/home/ubuntu/weil-launcher/lcompile.py` was
patched on the launcher host. The original is preserved there as
`lcompile.py.K1-FieldRingedScalar-1793020390.bak`.

The local published-object mirror deliberately excludes Lake `.trace` files.
Thus the server's transitive dependency repair in commit
`afad5bfa6ec0b4d9951265984050c14351882830` also needs local missing-object
diagnostics to take the existing fallback to the server. The fallback previously
recognized "failed to open file" and local-service exceptions, but not Lean's
"error: object file ... does not exist" diagnostic.

`lcompile-missing-transitive-fallback.patch` adds that case to the existing
fallback. It changes no concurrency setting, does not modify publication, and
does not retry ordinary elaboration errors on another service.

The five isolated tests exercise the real local-service reply processing with
synthetic reply archives, without Lean or SSH:

```
python3 test_lcompile_missing_fallback.py /home/ubuntu/weil-launcher/lcompile.py
```

The missing-object test failed against the original compiler. All five tests
passed against both the patched copy and the installed compiler. This directory
archives the deployed launcher change in the server repository; it does not
change a landing tool or the mirror service.

The launcher integrity guard restored the original compiler at 21:28:56 and
22:05:00 during this maintenance. The deployed patch is now registered using the
supported maintainer interface:

```sh
python3 /home/ubuntu/weil-launcher-all/integrity/check.py --accept /home/ubuntu/weil-launcher/lcompile.py
```

The guard's `manifest.json` and `pristine/weil-launcher/lcompile.py` were backed
up with suffix `.K1-FieldRingedScalar-1793020390.bak` before registration. Only the
compiler entry was updated. The guard remains running, with its other entries
unchanged. The compiler's final SHA-256 is
`5600325f3aa234b73656e7bff388fab31f765d8b67f5392b6f30a76f730a7a21`.
