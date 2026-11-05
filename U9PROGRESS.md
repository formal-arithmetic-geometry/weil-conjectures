
## 2026-11-05 K8 co-projection assignment
- Merged pr/2126 (087dc5065) then pr/2115 (437d24637). Preserved the b1 proper/compact exceptional adjunction proofs, moved the latter into the new UpperShriek module, and retained both versions' distinct K-flat, base-change, and Yoneda APIs.
- Route comparison: inspected iface-start VerdierDual users. The old native_compact_projection_formula route provides an existential projection iso, whereas the assigned theorem requires its geometric square and invertible exceptional mate. PR2126 now supplies canonical proper projection data and the geometric square directly. Route A via compactification is cheaper and preserves the target statement.
- Initial check: resolved-merge modules plus target and VerdierDual; compile exclusively with ucheck.
