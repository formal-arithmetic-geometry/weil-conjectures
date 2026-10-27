## Worker report

The module `Sheaf.AlgebraicGeometry.LocalSplitTorusExtensionPoints` states
`AlgebraicGeometry.localSplitTorusExtensionPoints_surjective` with one whole-proof
`sorry`. No definitions or proofs are added. The node's statement is unchanged.
Its statement dependencies gain the already landed `def-sfb-relative-split-torus`,
whose actual relative Hopf-spectrum construction is used.

Clause-by-clause correspondence:

- Nonzero commutative local ring C: `(C : Type u) [CommRing C] [IsLocalRing C]`.
  Mathlib's `IsLocalRing` extends `Nontrivial` and requires the local-ring unit
  condition, equivalent to having a unique maximal ideal. No separate,
  redundant nonzero hypothesis is needed.
- U = Spec C: every occurrence is `Spec (.of C)`, the recorded `Spec` construction.
- E and J commutative group schemes over U: `E J : Grp (Over (Spec (.of C)))`
  with `[IsCommMonObj E.X] [IsCommMonObj J.X]`. `Grp` packages `GrpObj`, i.e.
  multiplication, inverse and identity with all group diagrams. No field,
  smoothness, separatedness, finiteness or affineness hypothesis is imposed.
- Rank r >= 0 and T = G_m,U^r: `r : ℕ` and
  `relativeSplitTorus (Spec (.of C)) r`. This is the landed construction from
  the Hopf group algebra Γ(U)[Z^r], pulled back along U.toSpecΓ. Over the affine
  U it is the Laurent-coordinate split torus with multiplication of units.
- i and q are homomorphisms: their types are morphisms in `Grp (Over U)`, and
  `.hom.hom` is the underlying U-scheme morphism.
- i identifies T with the scheme-theoretic kernel:
  `_hkernel : IsPullback i.hom.hom (toUnit T.X) q.hom.hom η[J.X]`.
  This is precisely the cartesian square of q with the unit section of J.
  In particular it includes the equation q i = 1 and the kernel universal
  property, without selecting an unrelated isomorphism or map.
- J-sections lift fppf locally: `_hlocallySurjective` is
  `Presheaf.IsLocallySurjective (Scheme.fppfTopology.over U)
  (yoneda.map q.hom.hom)`. On every test U-scheme, the sieve where a section
  lifts is covering in the actual big fppf topology. This is sheaf exactness
  at the right endpoint, with no global lifting hypothesis.
- Y(C) = Hom_U(U,Y): `Over.mk (𝟙 (Spec (.of C))) ⟶ Y.X`.
- q:E(C)->J(C) surjective: `Function.Surjective` of the displayed map
  `fun e ↦ e ≫ q.hom.hom`.
- Fields: every `Field C` has `CommRing C` and `IsLocalRing C`, so the same
  theorem includes fields without a separate assertion or extra conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, `Spec.map`, from the recorded scheme and spectrum nodes.
  The module is publicly available through the relative-torus dependency.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`, from `def-pc-fppf-site`.
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`, the recorded
  site's slice construction.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, `Grp` morphisms;
  `IsCommMonObj` is the existing commutativity predicate. These are supplied
  by the torus import. They work over arbitrary base schemes.
- `Sheaf.AlgebraicGeometry.RelativeSplitTorus`: `relativeSplitTorus`, recorded
  by `def-sfb-relative-split-torus` (landed Q110, 2026-10-24). Its signature,
  docstring and complete body were read; it contains actual Hopf-spectrum data.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback`: `IsPullback`
  (available through the public dependencies), expressing the kernel directly.
- `Mathlib.CategoryTheory.Sites.LocallySurjective`:
  `Presheaf.IsLocallySurjective`, read including `imageSieve_mem`.
- `Mathlib.RingTheory.LocalRing.Defs`: `IsLocalRing`.

Proof dependencies retained as plain imports:
`WeilConjectures.AlgebraicGeometry.Descent` and
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`. The former supplies
`exists_isQuasicoherent_toDescentData_iso` and invertibility descent; the latter
supplies `Scheme.Modules.IsInvertible`. Pullbacks, the fppf-to-fpqc precoverage
comparison and fpqc subcanonicity/representable descent are available through
already required public imports. No import creates a cycle.

Sources read: local Stacks `etale-cohomology.tex`, theorem-picard-group
(Tag 03P8), and `groupoids.tex`, lemma-characterize-trivial-pseudo-torsors and
 definition-principal-homogeneous-space (Tags 0499 and 049A). They give the
Picard identification and the torsor/local-section criteria used in the node's
coordinatewise descent proof. The theorem docstring carries all four proof steps.

Edge cases checked before writing: rank zero is accepted by `r : ℕ`, with the
trivial torus and empty coordinate descent; fields are local rings; arbitrary
residue characteristic, nilpotents and non-Noetherian local rings are allowed.
The zero ring is excluded by Mathlib's local-ring class, just as in the node.
There is one explicit universe `u`, shared by C and schemes; test schemes range
over all objects of the big slice site. No independent smaller universe makes
the local lifting hypothesis vacuous. E and J have identity sections over the
nonempty base, so no nonemptiness premise has been added.

Searches (all via the prescribed msearch.py, with actual answers recorded in
sandbox searches.jsonl):

- LeanFinder: "An fppf exact extension of group schemes by a split torus is
  surjective on points over a local ring". Eight hits; `pointsPi_surjective`
  concerns products of rings and `GroupExtension.rightHom_surjective` assumes
  an abstract extension already surjective on its underlying groups. Neither
  supplies this theorem.
- Loogle: `"IsLocalRing", "Pic"`. One hit,
  `CommRing.Pic.instSubsingletonOfIsLocalRing`; it trivializes the algebraic
  Picard group but does not state scheme-point lifting.
- Mathlib grep: `splitTorus|split_torus|torus.*surjective|torus.*extension`,
  subdirectory AlgebraicGeometry. No hits.
- LeanSearch: "A torsor under a split torus over a local ring has a section".
  Eight abstract torsor/group-extension/module hits; no scheme statement.
- Project rg of `relativeSplitTorus|localSplitTorusExtensionPoints` in both
  `lean/WeilConjectures` and `lean/Sheaf` found the existing relative torus
  construction and consumers, but no existing statement of this theorem.
- Project rg of `localSplitTorusExtension|local_split_torus_extension|` followed
  by the item id in both source roots found no declaration for this node.

No STATEMENT-DISPUTED issue, statement correction, new node, or dependency
repair was needed. The example CompactObject Sheaf module has been withdrawn;
its node points to `WeilConjectures.CategoryTheory.CompactObject`, which was
read as the current example instead.

Validation: prescribed scompile.py compiled this file in sandbox and final
module modes cleanly (2.8 s and 1.5 s); every variable and universe is explicit.

## Second reading by NP

This is the dispatcher's single-worker delivery; the brief explicitly forbids
starting other agents. This section records a separate self-reading, not an
independent worker review; the maintainer's independent review follows delivery.
Reopened the node and module and compared the clauses above. In particular,
checked that IsPullback uses the unit section (not the identity of J), that the
torus is over Spec C rather than a field, that the local-surjectivity map is the
actual Yoneda image of q, and that the source of global points is U over itself.
Checked nonzero is inherited by IsLocalRing, both group objects have the
commutativity assumptions, and no rank-positivity or scheme finiteness condition
is present. The conclusion is exactly surjectivity of postcomposition with q.
No mismatch was found and no signature change was made after compilation.
