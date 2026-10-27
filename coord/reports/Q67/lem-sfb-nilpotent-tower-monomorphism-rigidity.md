## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.NilpotentTowerMonomorphismRigidity`.
Main declaration: `AlgebraicGeometry.isIso_of_nilpotentTower`. It states the item's
unchanged assertion, with `sorry` as its only proof. No definitions, helper theorems,
new DAG nodes, dependency repairs, or statement corrections are needed.

The inherited BLOCKED ending concerned a stage-1 re-split: O1 already delivered the
accepted split. I read the live node, O1's report, and the stage handoff paragraph
of coord/brief-stage2.md. This node has no Lean record and coord/queue.tsv lists it
at stage 2. This delivery retains the accepted split and adds only the `lean` field.
There is no coord/repair-notes/lem-sfb-nilpotent-tower-monomorphism-rigidity.json.
The earlier dry run with the empty retained sandbox reported a missing node file;
the delivery now contains that file and the module and report.

Source read: literature/stacks-project/flat.tex, lemma-monomorphism-isomorphism,
Tag 0CTJ, including its entire proof. The source calls the transition kernels
locally nilpotent; the accepted node correctly spells this out as elementwise
nilpotent. There is no uniform nilpotence exponent. The declaration docstring
carries all nine steps of the accepted DAG proof, including the explicit
unit calculation and the final cancellation for the original source T.

Hypothesis and clause correspondence:

- Schemes and commutative rings in the size convention: `universe u`,
  `D : ℕᵒᵖ ⥤ CommRingCat.{u}`, and `{T : Scheme.{u}}`. There is no characteristic,
  Noetherian, nonzero, or finite-presentation assumption.
- The inverse sequence `(A_n)_{n >= 1}`: `D.obj (op n)` denotes the paper's
  `A_{n+1}`. Indexing at zero is just a shift, with the first stage present.
  `D.map (homOfLE (Nat.le_succ n)).op` is the transition from stage `n+1` to `n`
  in Lean's indexing. The functor laws encode identity and composite transition
  maps; every inverse sequence gives exactly such a functor by finite composition.
- Surjective transitions: `hsurj : ∀ n : ℕ, Function.Surjective
  (D.map (homOfLE (Nat.le_succ n)).op).hom`.
- Kernels consist of nilpotent elements: `hnil : ∀ (n : ℕ)
  (x : D.obj (op (n + 1))), (D.map (homOfLE (Nat.le_succ n)).op).hom x = 0 →
  IsNilpotent x`. The exponent may depend on both `n` and `x`. Successor
  conditions give the conditions for all longer transitions: surjectivity is
  closed under composition, and if a composite kills x, nilpotence of its image
  in the intermediate ring puts some power of x in the first kernel, where a
  further power vanishes. Thus no condition on a non-successor arrow is lost.
- `A = inverse limit A_n`: `limit D`, the chosen categorical inverse limit of
  commutative rings. Mathlib.Algebra.Category.Ring.Limits constructs these
  limits and preserves them under the forgetful functor to types. For this
  countable index, existence is supplied by Mathlib with no added hypothesis.
  The chosen categorical model is canonically the ring of compatible tuples.
- The morphism `h : T → Spec A`: `(h : T ⟶ Spec (limit D))`.
- Monomorphism as injectivity on Hom(B,-) for every scheme B: `[Mono h]`.
  Mathlib's Mono.right_cancellation quantifies over every test object and every
  pair of maps; it is exactly that injectivity, without a representability or
  pointwise shortcut.
- Locally finite type: `[LocallyOfFiniteType h]`, the dependency's recorded
  Mathlib class. QuasiCompact h is not assumed.
- Every canonical `Spec A_n → Spec A` factors through h:
  `hfactor : ∀ n : ℕ, ∃ a : Spec (D.obj (op n)) ⟶ T,
  a ≫ h = Spec.map (limit.π D (op n))`. This uses the actual canonical projections,
  not arbitrary maps. No compatible choice of factorizations is assumed;
  compatibility follows from monicity as in proof step 1.
- Conclusion: `IsIso h`. This means that this very morphism is an isomorphism,
  rather than an unconnected existential isomorphism of the schemes.

Statement dependency declarations read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (full structure
  signatures and their docstrings read in Scheme.lean).
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map` (their definitions,
  signatures, docstrings, and contravariant composition law read).
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; its finiteType_appLE condition is
  equivalent to the node's affine-cover definition, as the dependency record
  explains. The companion `AlgebraicGeometry.QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` was read, but it is not an
  additional hypothesis in this item.
- def-weil-size-convention is a metatheoretic convention with null declaration;
  explicit universe polymorphism implements it here. Countability of the
  diagram is fixed by the item's sequence, so no independent large index
  universe or smallness restriction on the rings is introduced.

Additional existing Mathlib interfaces used, with no private copies:
`CategoryTheory.Limits.limit`, `CategoryTheory.Limits.limit.π`,
`CategoryTheory.homOfLE`, `CommRingCat.Hom.hom`, `Function.Surjective`,
`IsNilpotent`, `CategoryTheory.Mono`, and `CategoryTheory.IsIso`.

The proof dependencies are imported privately, as required for stage 3:
Prime.Topology for both basic-open nodes; Prime.Homeomorph for the all-element
powers homeomorphism; AffineScheme for the affine basis and compactness;
OpenImmersion for open immersions, principal localization, and their base changes;
Morphisms.QuasiSeparated for affine quasi-separatedness and qcqs permanence;
Sheaf.AlgebraicGeometry.MonomorphismFiniteTypeComposite for
`Scheme.Hom.monomorphism_properties_of_locallyOfFiniteType_comp`;
WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization for
`Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite`;
Morphisms.Finite / Integral for finite and integral morphisms; Morphisms.Affine
for affine morphisms; Limits.Shapes.Pullback.HasPullback for fibre products;
GroupTheory.MonoidLocalization.Away for Localization.Away. Statement dependencies
Scheme and Morphisms.FiniteType are public imports. No import cycle is created.

Edge cases checked before writing:

- Constant tower: the canonical stage map is an isomorphism, so a factorization
  gives a section of h; monicity gives the other inverse identity.
- Zero first ring / empty spectrum: nil-kernel surjections then force every
  later ring to be zero (1 lies in the nil kernel); the limit and its spectrum
  are zero and empty. A scheme mapping to the empty base is empty. There is no
  Nontrivial instance that would exclude this case.
- T can be non-quasi-compact. The proof reduces to a finite affine neighbourhood
  of the common stage image and then cancels the original h. No compactness
  typeclass is present in the signature.
- A_n = k[t]/(t^(n+1)), with limit k[[t]]: the limit projection kernel need not
  be nilpotent; hnil is imposed only on transitions, so this case is retained.
- A transition may have an elementwise nilpotent ideal that is not nilpotent.
  Quantifying IsNilpotent separately for x retains this case.
- The first stage is `op 0`, corresponding to the paper's n=1. No stage or
  factorization is omitted, and there is no empty-index variant in the item.

Searches for an existing declaration (all performed for this item):

- msearch.py leanfinder: "A locally finite type monomorphism to the spectrum
  of an inverse limit of surjective rings with nil kernels is an isomorphism
  if every stage factors through it". Eight hits: product-spectrum immersion
  criteria, flat-mono isomorphism, closed immersion criteria, and eventual map
  equality for scheme limits. None states nilpotent-tower effectiveness.
- msearch.py loogle: "AlgebraicGeometry.LocallyOfFiniteType,
  CategoryTheory.Mono, CategoryTheory.IsIso". Zero hits.
- msearch.py leansearch: "locally finite type monomorphism inverse limit rings
  nilpotent kernels isomorphism". Eight hits: finite type instances,
  idempotent lifting, kernel of a mono, and a profinite group limit result;
  none is this scheme statement.
- msearch.py grep in AlgebraicGeometry: regex
  `nilpotent.*tower|nilpotentTower|isIso.*[Ll]imit|[Ll]imit.*[Mm]ono`.
  Five unrelated matches in Gluing, Limits, SmallAffineZariski, and Cover/Open.
- rg on lean/WeilConjectures and lean/Sheaf for nilpotent tower terminology,
  monomorphism/isomorphism and inverse-limit terminology, and Tag 0CTJ:
  only unrelated generic maps, etale limit-descent results, or explanatory
  prose; no declaration for this item.
- rg on lean/WeilConjectures and lean/Sheaf for the full blueprint id: no match.
- rg of Mathlib, lean/WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for `isIso_of_nilpotentTower`: no collision.
- Read Mathlib.Algebra.Category.Ring.Limits and the generic limit interface:
  the existing categorical limit and projections suffice, so no new notion
  or duplicate inverse-limit definition is introduced.

No statement dispute or unresolved node fault. The only node delta is `lean`.
All variables and the universe are explicitly bound, with autoImplicit disabled.
The module compiles through scompile.py in both sandbox and library module modes
(1.5 seconds each), with no reported errors or warnings. Only `sorry` remains,
as required for stage 2.

## Second reading by Q67

I reopened the node and module in a separate checking pass; no other agents were
started, as required by the dispatcher. This is a worker's second pass, not a claim
of an independent maintainer review. I checked each binder and the conclusion
against the unchanged statement and the full Stacks 0CTJ source. The inverse
sequence is oriented correctly: homOfLE n (n+1) is reversed before D.map, and
Spec.map reverses the limit projection. The factorization equation consequently
has source Spec A_n and target Spec A. Naturality is not imposed on the a's.
Mono h expresses cancellation of maps into T, not injectivity on points.
Local finite type is the recorded class, with no added quasi-compactness.
IsNilpotent x is elementwise, not IsNilpotent of an ideal, and the canonical
limit is the categorical ring limit with its real projections. Universe u is
shared by rings and schemes, covering the zero ring and arbitrary scheme T.

I also checked the nine proof paragraphs against the accepted split. During this
pass I corrected a composition-order typo in the final docstring paragraph:
with diagrammatic order the cancellation identity is `(h s) h = h`, giving
`h s = identity` on T. The mathematical signature did not change. No binder,
hypothesis, stage, or conclusion mismatch remains. The maintainer's independent
review is still required by the delivery workflow.
