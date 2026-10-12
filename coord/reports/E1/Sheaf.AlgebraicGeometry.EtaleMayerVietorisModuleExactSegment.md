## What changed

Proved `AlgebraicGeometry.Etale.exists_module_mayer_vietoris_exact_segment` without changing
its signature or existing docstring. Added a fully proved private helper
`module_open_pullback_cohomology_equiv`, constructing the three required cohomology
identifications using the actual pullback schemes. Added proof-only imports of
`Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback` and
`Sheaf.AlgebraicGeometry.EtalePullbackForgetModules`. Updated the item's DAG proof to match.

The final proof uses the first exact sequence in `etale_mayerVietoris_pullback` at the
identity of Z; no pullback naturality or second sequence is needed. Exactness is transported
explicitly in both directions, using inverse equivalences on kernels and preimages.
Local compilation succeeds. No vanishing assumption, torsion assumption, or additional
hypothesis was introduced. The construction covers degree zero, empty opens, and repeated
opens because neither the helper nor the cover argument requires nonemptiness or strictness.

## Proved and sorry left

Proved the item's sole former sorry:
`AlgebraicGeometry.Etale.exists_module_mayer_vietoris_exact_segment`
(node `lem-weil-pbc-etale-mayer-vietoris-module-exact-segment`).
The private helper is also fully proved. No sorry remains in the delivered module;
no new module or sorry was added. The imported existing declaration
`AlgebraicGeometry.Etale.etale_mayerVietoris_pullback`
(node `lem-weil-pbc-etale-mayer-vietoris-pullback`) still has its existing sorry and is the
next substantive cohomology dependency. This is a proof from existing stated declarations,
not a claim that the whole transitive closure is sorry-free.

## No longer needed

No existing import was removed. The old direct route through
`lem-weil-pbc-etale-mayer-vietoris` (`Sheaf.AlgebraicGeometry.EtaleMayerVietoris`) and
`lem-weil-pbc-sheafH-ext-derived-comparison`
(`Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`) is not needed by this module's
proof; it uses the existing Sheaf.H interface of Mayer--Vietoris pullback instead.
These nodes may remain dependencies of that existing theorem or of other targets, so this
is not a claim that they can be globally deleted. All other original proof dependencies
remain used, with the open-immersion geometry implemented by Mathlib's restriction iso.
No new split nodes.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original DAG omitted the available Mayer--Vietoris
pullback declaration from its direct dependencies; its first sequence provides precisely
the Sheaf.H segment needed and avoids a separate derived-to-Ext comparison in this item.
The node route now records this use. The required section I of coord/delivery-errors.md
is not present in this checkout; the existing stage instructions and delivery checks
were followed.

## Second reading by E1

1. Compared the sole delivered module with the repository version. PASS: the existing
   theorem signature and docstring are byte-for-byte unchanged, and no definition or
   public import changed. The only new declaration is a private, fully proved helper.
2. Compiled the module with lcompile.py: exit 0, no warnings. PASS: no sorry or forbidden
   declaration mechanism occurs in the delivered file. A scratch-copy #print axioms of
   exists_module_mayer_vietoris_exact_segment lists exactly propext, Classical.choice,
   Quot.sound and sorryAx. The existing etale_mayerVietoris_pullback is still open; this
   delivery does not claim a closed transitive proof. The forget-modules comparison is
   already proved in the repository.
3. PASS: no split-off statement, new public statement, or new node was added. Checked
   the private helper's scheme-isomorphism direction, composite equality, module
   composition isomorphisms, forgetful comparisons and additive cohomology equivalence.
   Degree zero and empty or repeated opens introduce no additional assumption.
4. PASS: the first exact sequence of the existing pullback theorem supplies precisely
   the needed segment; no naturality or derived-to-Ext comparison is needed here.
   Searched repository cohomology/pullback comparisons and Mathlib exactness transport
   with a distinct grep query; no shorter replacement of the geometric comparison was
   found. Both added imports serve the proof only and are plain imports. The No longer
   needed section lists both old proof dependencies omitted by the new route. Checked
   sk-thm-p1.json realized: neither omitted dependency realizes a protected unit step,
   so the unit route is preserved.
5. PASS: node diff changes only proof, proof_deps and proof_origin. Their step uses and
   union agree with the explicit geometric identification, cohomology transport and
   Mayer--Vietoris extraction in Lean. No statement or Lean signature metadata changed.

Second-reading changes: appended this review only; no repair to Lean or DAG was needed.
