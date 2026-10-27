# O2 qcoh groupoid extraction maintenance

The returned delivery 52152add7c20 was required to move four generic definitions
out of AlgebraicSpaceInvertibleDescent into a definition-owned module. Its repaired
item no longer depends on the invertible-descent theorem. tools/stage2_delivery.py
therefore excludes that consumer node from the delivery prerequisite closure and
rejects the required consumer module as ownerless.

This maintenance commit lands only the requested shared-library extraction and its
record repair, so the worker can deliver its item against a consistent base. It
also records the consumer theorem's dependency on the new definition owner. The
four relocated definitions preserve full names, signatures and bodies exactly; the
retained structure and theorem, including proof, are byte-identical. Only the moved
ownership docstrings change. The worker's item and the landing tools are untouched.

Backups are beside all changed paths with suffix
.maint-O2-qcoh-20261024.bak; for newly created paths the backup records ABSENT.

Validated one file at a time with tools/lean_file.sh and a 60 second limit, in the
private O2-maint-qcoh build mirror:

```text
lean/Sheaf/AlgebraicGeometry/OrdinaryEtaleIdentification.lean
Compiled in 24.6 s

lean/Sheaf/AlgebraicGeometry/AlgebraicSpaceInvertibleDescent.lean
Compiled in 17.6 s

lean/.sandbox/O2-maint-qcoh/SpaceQcohGroupoidEquivalence.lean
Compiled in 17.3 s
```
