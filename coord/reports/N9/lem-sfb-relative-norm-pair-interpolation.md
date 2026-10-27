## Worker report

Module: `Sheaf.AlgebraicGeometry.RelativeNormPairInterpolation`.
Main declaration: `AlgebraicGeometry.exists_relative_norm_pair_interpolation`.
This is a stage-2 statement: its whole proof is `sorry`. Three real-data convenience
constructions belong to the item: `normInterpolationRestriction` composes the normalized
pullback of sections with composition and tensor-power comparisons;
`normInterpolationPair` applies the existing norm twice and the existing two-section family;
`normInterpolationPencil` spells out generation and the canonical coordinate-map properties.
They introduce no independent mathematical notion or postponed theorem.

Hypothesis and clause correspondence:

- The field k is `[Field k]`; the integral finite-type k-algebra is `[CommRing A]`,
  `[IsDomain A]`, `[Algebra k A]`, `[Algebra.FiniteType k A]`. The affine base is literally
  `Spec (.of A)`. The fraction field K is any `[Field K] [Algebra A K] [IsFractionRing A K]`,
  retaining its specified canonical embedding of A. This permits every model of Frac A.
- The closed point is `s : Spec (.of A)` with `hs : s.asIdeal.IsMaximal`; its maximal ideal
  is nonzero by `hs0 : s.asIdeal ≠ ⊥`. Maximality is exactly closedness by Mathlib's
  `PrimeSpectrum.isClosed_singleton_iff_isMaximal`.
- The morphism is `p : Y ⟶ Spec (.of A)` with `[Surjective p] [IsHProjective p]`.
  `[IsIntegral Y]` states integrality. Finite type over k is `LocallyOfFiniteType` and
  `QuasiCompact` on `p ≫ Spec.map (algebraMap k A)`, making explicit the structure morphism.
- `hpure` quantifies over every algebraically closed field Ω in the scheme universe and
  every geometric point `q : Spec Ω ⟶ Spec A`, and says `(pullback p q).IsPureDimension 1`.
  This is exactly pure one-dimensional geometric fibres, including the convention for
  empty schemes. The tests are in universe u, not an independent smaller universe.
- The generic curve is literally `pullback p (Spec.map (algebraMap A K))`; its structural
  projection is `pullback.snd`. `Smooth` and `GeometricallyIntegral` on that projection
  state exactly smoothness and geometric integrality over K.
- The specified embedding is `i : Y ⟶ ℙ(ULift (Fin (D+1)); Spec A)` with
  `[IsClosedImmersion i]` and `hi` saying that it is over the base. `D : ℕ` includes D=0.
  `hL` binds the named L to the actual tensor pullback of `ProjectiveSpace.twist ... 1`.
  It is the node's equality L=i*O(1), not an additional positivity hypothesis or arbitrary
  line bundle. The relative twist is the existing integral-Proj twist pulled back along
  `ProjectiveSpace.toProjInt`, as its definition and docstring specify.
- `[Group G] [Finite G]` and `ρ : G →* Aut (Over.mk p)` encode the action over U.
  `hfaithful` is injectivity only after base change to K and forgetting the over-category.
  This is faithfulness on C, not an assumption about the special fibre's action.
- The existential `V` is the affine open U': `s ∈ V ∧ IsAffineOpen V`. Its inverse image
  `p ⁻¹ᵁ V` is canonically Y_U'. The exponent is `n : ℕ` with `1 ≤ n`.
- `a b : ((tensorPullback (p ⁻¹ᵁ V).ι).obj (L.tensorPow n)).sections` are ordinary sections
  of the restriction of L^n. They are not arbitrary norm sections or invariant lifts.
- `es,hes` and `eK,heK` exhibit the original special and generic fibres inside this open
  inverse image; their commuting triangles uniquely determine these maps because an open
  immersion is mono. These are existential factorization data, not extra assumptions.
  They ensure the conclusions are on the original `p.fiber s` and C themselves.
- `normInterpolationRestriction` pulls a back along es/eK, compares the composed pullback
  with the original fibre inclusion using the displayed equality, and applies
  `boundaryPullbackPowIso`. Its result is exactly a_s or a_K in L_s^n or L_K^n; similarly b.
- `normInterpolationPair` uses `pencilNormSection` of the recorded orbit-norm node on
  those actual restricted ordinary sections, with the `Over.pullback` action on the fibre.
  Its codomain is `(pencilOrbitBundle ρ_fibre L_fibre).tensorPow n`. This is B_fibre^n
  under the canonical finite tensor/pullback comparison, not a newly chosen bundle.
- The first `normInterpolationPencil ... false` states existence of the invertibility
  witness and `ht : Epi (M.freeHomEquiv.symm t)`, and `IsFinite` of the exact
  `ProjectiveSpace.homOfGeneratingSections` morphism. These are generation and the finite
  special-fibre pencil into projective one-space over the actual residue field.
- The second `normInterpolationPencil ... true` states the same generation and finiteness
  over K, together with `Surjective` and `∃ W : C.Opens, Nonempty W ∧ Etale (W.ι ≫ φ)`.
  It thus includes all three generic pencil clauses. The false case imposes no
  surjectivity or etaleness requirement. Bool only selects which of the two node clauses
  to expand; both expansions use the same existing coordinate construction.
- No infinitude hypothesis on k or the residue field, no separability of the action,
  no reducedness of the special fibre, and no characteristic/group-order condition occur.

Recorded dependency declarations used (source signatures and docstrings read):

- `Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil`:
  `Scheme.Modules.pencilOrbitBundle`, `pencilNormSection`, `pencilSectionPair` and their
  finite enumeration/tensor/power/section definitions. No copy of a norm is defined.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`,
  `tensorPow` and the module monoidal structure.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`: `Proj.twist`;
  the relative projective-space specialization is the existing `ProjectiveSpace.twist`
  of `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`; `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
  records the `Over.pullback` convention and base-change projections.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`: `GeneratingSections`, whose
  epimorphism field is the exact `Epi (M.freeHomEquiv.symm t)` condition used here.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`:
  `ProjectiveSpace.homOfGeneratingSections`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- The already recorded canonical section and tensor-power interfaces are
  `Scheme.Modules.tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`
  (`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`) and
  `boundaryPullbackPowIso` (`WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`).
  Their existing owning nodes and the relative twist node are cited directly in stmt_deps.

All stated proof-dependency modules are imported as proof imports unless already public
statement imports. The seven-step natural-language proof is in the theorem docstring.
The source PDF was read at https://www.numdam.org/item/10.5802/aif.1575.pdf, p.606, §3.4.
That paragraph gives the lifting and density argument; the norm replacement is explicitly
the agent-written argument already present in the item's accepted DAG proof.

Edge cases checked: finite base/residue fields are allowed; the nonzero maximal ideal
excludes precisely the closed generic point/field base case and ensures the perturbation
lattice is infinite. The special fibre may be nonreduced and its action unfaithful. The
trivial group is allowed. n=0 is excluded by the stated positive exponent. D=0 is typed
without excluding it by hand; the other geometric hypotheses make it impossible. Empty Y
is excluded by integrality and surjectivity; pure dimension itself retains the empty
scheme convention. Inseparable power maps on the special fibre remain finite. Characteristic
dividing |G| is allowed. No action law or base-commutation condition is silently omitted:
they are supplied by the monoid homomorphism into automorphisms in `Over`.

Searches (2026-10-24):

- `msearch.py ... leanfinder "simultaneous special and generic norm pair interpolation
  sections finite morphism etale"`: 8 hits, standard-etale presentations, standard-smooth
  etale coordinates and etale loci; none states interpolation of norm pencils.
- `msearch.py ... loogle "Scheme IsIntegral Smooth IsHProjective IsFinite Surjective Etale"`:
  no hits, unknown identifier Scheme in the remote index. Source searches and compiler
  checks supply the actual current declaration names instead.
- `msearch.py ... grep "interpolation|pencilNorm|norm.*pencil" AlgebraicGeometry`: 0 hits.
- `msearch.py ... leansearch "projective relative curve sections special generic fibre
  simultaneous finite separating norm pencil"`: 8 hits, Proj chart sections, finite
  postcomposition and properness; none is this assertion.
- `rg` over `lean/WeilConjectures` for `relative.norm.pair|interpolation|pencilNormSection`:
  unrelated polynomial interpolation only. Exact item-id grep has no source match.
- `rg` over `lean/Sheaf` finds the existing norm in AmpleCurveTwoSectionPencil and its
  use in SeparatingPairOpen, plus the downstream InvariantLocalCurvePencils theorem.
  The latter has a different conclusion (normal models and invariant local pencils),
  and its proof's interpolation paragraphs do not constitute a separate declaration.
- Full new names were searched in the source, Sheaf, and dag/lean_names_upstream.json:
  no existing declaration. The helpers only compose the recorded constructions.

No statement dispute, correction, new node, or dependency repair is needed.

## Second reading by N9

Final worker self-check: compared the theorem binders and both expanded pencil predicates
against the original node. Checked that the ordinary sections are shared by the two
fibres, that the restriction maps are canonically fixed by their triangles, that the
norms use the base-changed action, and that the generic open is explicitly nonempty.
The independent review is the maintainer's delivery review prescribed by the dispatch;
no second agent was started by this worker.
