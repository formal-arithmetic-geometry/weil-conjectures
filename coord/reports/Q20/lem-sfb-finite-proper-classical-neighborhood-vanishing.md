## Worker report

The module `Sheaf.SixFunctors.FiniteProperClassicalNeighborhoodVanishing` states
`AlgebraicGeometry.ProEtale.finiteProper_classical_neighborhood_vanishing`.
Its sole theorem has proof `by sorry`; it introduces no definitions, axioms, or instances.
Only the item's `lean` field changes. There is no statement correction or disputed statement.
No maintenance repair note for this item was present.

The source was read in the current blueprint's
`sec-six-functors-basics/sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.proof.md`,
including its uniform bound and Transfer paragraph, and in the local Stacks source
`etale-cohomology.tex`, lemma-cohomological-dimension-proper (Tag 095U).
The latter applies to all torsion abelian sheaves, without a prime-to-characteristic hypothesis.

The statement uses the published fixed-coefficient presentation, not a new module category.
`Sheaf (Scheme.ProEt.topology Z) (ModuleCat A)` is the ordinary category of modules over
the constant ring sheaf: discrete scalar actions uniquely extend to locally constant scalar
sections. The recorded `finiteCoefficientRealization` realizes exactly this category in
`FiniteCoefficientModules Z A`, with its exactness and equivalence already supplied in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`. Consequently all sheaves of the node are
covered. This is also the presentation used by the recorded
`det-pe-classical-sheaves-modules` declaration. No topology parameter on `A` is necessary
in this fixed-scalar presentation: the coefficient ring is constant, with the discrete
interpretation stipulated in the source. The finite-discrete ring identifications in the
proof dependencies provide the same identification in the condensed presentation.

Each hypothesis and clause has the following counterpart:

| Node text | Lean rendering |
| --- | --- |
| A finite commutative ring | `(A : Type (u + 1)) [CommRing A] [Finite A]` |
| A proper morphism of schemes f:X -> Y | `{X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]` |
| An integer e >= 0 | `(e : ℕ)`; casts to `ℤ` in the degree inequality |
| All fibres of every base change have dimension <= e | `_hbound : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T), topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞)` |
| V -> Y is an object of the small pro-etale site | `(V : Y.ProEt)`; its morphism is `V.hom` |
| V is affine | `[IsAffine V.left]` |
| V is weakly contractible in Y_proet | `_hV : (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V` |
| Z = X times_Y V | The literal chosen `pullback f V.hom`, with no independently supplied scheme |
| h:Z -> V is the projection | The literal `pullback.snd f V.hom`, with no independently supplied map |
| H is an ordinary A-module sheaf on Z_proet | `(H : Sheaf (Scheme.ProEt.topology (pullback f V.hom)) (ModuleCat.{u + 1} A))` |
| H is classical, meaning H is isomorphic to nu_Z^* F | `_hH` existentially quantifies an etale module sheaf `F` on this very pullback, and an isomorphism from `(comparisonUpperStar ...).obj F` to `H` |
| H[0] | `(DerivedCategory.singleFunctor _ 0).obj H` in each conclusion |
| Every integer q > 2e | `(q : ℤ) (_hq : 2 * (e : ℤ) < q)` |
| Cohomology sheaf of Rh_*(H[0]) is zero | First `IsZero`, with `DerivedCategory.homologyFunctor _ q` of `(lowerStar ... (pullback.snd f V.hom)).rightDerivedFunctor.obj ...` |
| H^q RGamma(Z_proet,H[0]) is zero | Second `IsZero`, with `DerivedCategory.homologyFunctor (ModuleCat A) q` of `(globalSectionsFunctor ... (pullback f V.hom)).rightDerivedFunctor.obj ...` |
| Both conclusions hold | Conjunction `∧`, for the same H, q, V, and e |
| All classical sheaves on Z, without descent from X | `H` and its etale witness `F` live directly on Z; no witness on X occurs |
| No Noetherianity, constructibility, or invertible additive exponent | No such binder or condition occurs anywhere in the signature |

All universes and variables are explicit, with `autoImplicit false`. The site is the
published small site (`Scheme.{u}`, objects in `Type (u+1)`, morphisms in `Type u`),
and module and set sheaves use the common larger coefficient universe `u+1`.
The base-change quantification uses the scheme universe, matching the existing
`finiteProper_classical_truncation` convention. No site object/morphism universe equality
is imposed. A finite coefficient ring can always be represented in this universe.

The right derived functors are the published total K-injective `Functor.rightDerivedFunctor`,
not `Functor.rightDerived q` and not an arbitrarily chosen bounded resolution. Their domain
and codomain are unbounded `DerivedCategory`; only the input `H[0]` is bounded below.
`globalSectionsFunctor` is evaluation at the actual terminal pro-etale object of Z.
`lowerStar` is restriction along scheme base change, with the specified section formula.
These constructions are the fixed-scalar presentations of the recorded ordinary operations.

Dependency declarations were read with their source docstrings and signatures:

- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
  `AlgebraicGeometry.baseChange_fiber` and `baseChange_iterated`; scheme base change is
  the recorded `Limits.pullback`, not the module-only primary declaration.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim : WithBot ℕ∞`, with bottom for the empty scheme.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and its topology; reexported by the imported framework.
- `sk-def-pe-weak-contractible`:
  `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`,
  `CategoryTheory.GrothendieckTopology.IsWeaklyContractible`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.snd`, reexported by base-change conventions.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`,
  `finiteCoefficientRealization`, `finiteCoefficientRealization_exact`,
  and `FiniteCoefficientModules` identify the fixed-scalar presentation as explained above.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` reexports the ordinary
  operations, their constant-ring and intrinsic presentations; the existing fixed-scalar
  `AlgebraicGeometry.ProEtale.lowerStar` is used, with the ordinary total right derivation.
- `sk-def-sfb-derived-categories`:
  `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and the existing
  `CategoryTheory.Functor.rightDerivedFunctor` (its Grothendieck-category specialization).
  `DerivedCategory.singleFunctor` and `DerivedCategory.homologyFunctor` are Mathlib's
  localization functors, read in `DerivedCategory.Basic` and `HomologySequence`.
- `def-weil-pbc-sites-and-cohomology`: `Sheaf.CategoryTheory.SiteCoveringAxioms`
  reexports the site/cohomology convention. For total sections, the existing
  `AlgebraicGeometry.ProEtale.globalSectionsFunctor` is read in and imported from
  `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`.
- `det-pe-classical-sheaves-modules`:
  `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`,
  `AlgebraicGeometry.ProEtale.proEtaleClassicalSheavesModules`, especially its last clause
  identifying classicality with exactly the essential-image hypothesis `_hH`.

Every recorded proof-dependency module that has a declaration is imported without `public`
when used only for the proof plan. The already-public properness, weak contractibility,
classicality and operation modules also cover their repeated proof-dependency entries.
`lem-pc-separated-quasi-separated` has no module record; its scheme fact is covered by the
existing Mathlib properness imports. No import cycle is introduced: in particular the
consumer `FiniteProperClassicalTruncation` is not imported. The declaration docstring gives
all five proof steps, including the explicit sheaf-of-pairs argument needed to transfer
weak contractibility to the localized site.

Edge cases checked before writing:

- e=0 includes every integer q>0; no positive-dimensional hypothesis is inserted.
- The zero ring is allowed by `CommRing` and `Finite`; its modules vanish and the
  proof's torsion annihilator can be chosen as 1.
- The zero sheaf is included, and is a classical sheaf.
- Empty X, V, or Z is allowed. Fibre dimension is bottom, hence satisfies the bound;
  the conclusions are zero sheaves/modules in the usual sheaf categories.
- Residue characteristic dividing the additive exponent is allowed. Tag 095U is a
  torsion theorem, not a prime-to-characteristic theorem.
- Non-Noetherian weakly contractible affine neighborhoods and nonconstructible classical
  sheaves are included. The etale witness is on Z and need not descend to X.
- The bound does not assert vanishing at q=2e, and no negative-degree claim is added.

Searches for an exact existing statement:

- `msearch.py ... leansearch "Vanishing of classical finite coefficient proetale sheaf
  cohomology on proper schemes over weakly contractible affine base"`: eight hits on affine
  global-section vanishing, light condensed categories, finite proper morphisms, and module
  finite presentation. None states this theorem.
- `msearch.py ... leanfinder "Classical torsion proetale module sheaf proper weakly
  contractible affine neighborhood cohomology vanishes above twice fiber dimension"`:
  eight hits on affine transition limits, qcqs section vanishing, and formally etale
  cotangent homology. None matches.
- `msearch.py ... loogle '"higherDirectImage"'`: zero hits.
- `msearch.py ... grep 'weaklyContractible|classical.*[Vv]anish|[Cc]ohomological[Dd]imension'`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the target declaration and
  `classical.*[Vv]anish|[Vv]anish.*[Ww]eakly`: no matching declaration. Nearby material
  concerns unbounded truncations, affine evaluation bounds, or vanishing detection.
  `FiniteProperClassicalTruncation` cites this item in its proof plan but does not state it.
- The required `grep -rn` for this node id in `lean/WeilConjectures` returned no match.

Validation: `scompile.py Q20 lem-sfb-finite-proper-classical-neighborhood-vanishing <module>`
passed the sandbox and library-module checks in 3.6 and 4.0 seconds, respectively, with no
errors or warnings. The JSON signature is copied verbatim from the theorem header;
JSON uses indent 1, Unicode, and a final newline. Every Lean line is at most 100 characters.

## Second reading by Q20

The dispatcher explicitly forbids starting other agents, so this section records a separate
second pass by the same worker, not a claim of independent review. The maintainer's
independent delivery review remains required.

I reopened the node's statement and compared the final theorem header against each clause.
`[Finite A]` and `[CommRing A]` match finite commutative coefficients. `f` and `[IsProper f]`
match the proper morphism. `_hbound` quantifies all base changes and all their fibre points;
there is no substitution of only the fibres of f. `V : Y.ProEt`, `[IsAffine V.left]` and
`_hV` keep the ambient-site weak-contractibility hypothesis. Both occurrences of Z are the
same literal pullback, and the direct image uses its second projection. `H` is arbitrary
on that Z; its etale witness also lives on Z, so the statement has not silently required
descent from X. The essential-image condition is exactly the final equivalence in the
recorded classical-module dependency. Both `IsZero` clauses take cohomology in degree q
of the total unbounded derived operation on H in degree zero. The inequality is strict
and casts e to integers, so equality q=2e is not included. The global sections functor
is taken on Z itself, not evaluation of the direct-image sheaf before deriving.
The absence of a topology parameter is justified by the existing canonical realization
of fixed-scalar modules over the constant ring sheaf. There are no private copies of
notions, extra hypotheses, omitted clauses, unbound variables, or data defined by sorry.
No statement mismatch was found and no statement change was necessary.
