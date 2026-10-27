## Worker report

States `AlgebraicGeometry.exists_almostHomogeneous_potential_smooth_cover` in
`Sheaf.AlgebraicGeometry.AlmostHomogeneousPotentialSmoothCover`, with one named
`theorem` and its proof `sorry`. There are no new definitions, helper theorems,
new nodes, dependency repairs, or changes to the natural-language statement.
The ten-step proof is included in its docstring.

Source checked: Anantharaman, *Schémas en groupes, espaces homogènes et espaces
algébriques sur une base de dimension 1*, Proposition 4.2.3 (OCR 4,2,5), printed
pp.58–59, and Appendix II, Corollaries 2–3, p.73, primary Numdam scan:
https://www.numdam.org/article/MSMF_1973__33__5_0.pdf . The source's smooth
normalized group and space supply the required models; its neutral group has
open geometric orbits equal to the connected components. The last two DAG
proof steps explain the composite's integrality and finite underlying fibres
without module-finiteness of the normalized base. The current latest blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md` was also read; this is a supporting
node, not the blueprint unit's own statement.

Clause-by-clause rendering:

- `R K : Type u`, `[CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]`, `hRdim : ringKrullDim R = 1`, and
  `hRsemi : Finite {m : Ideal R // m.IsMaximal}` express precisely the base ring.
  `[Field K] [Algebra R K] [IsFractionRing R K]` makes K its fraction field.
  `Spec (.of R)` is S. Giving K explicitly covers every choice of fraction field.
- `G X : Over (Spec (.of R))` are the given structure morphisms. `[GrpObj G]`
  includes actual multiplication, identity, inverse and their group identities.
  `[ModObj G X]` is an actual scheme action satisfying its two identities.
  Neither requires commutativity.
- G's `[IsSeparated G.hom] [Flat G.hom] [LocallyOfFiniteType G.hom]
  [QuasiCompact G.hom]` give separated, flat and finite type. Mathlib's separated
  predicate is exactly closed immersion of the diagonal.
- X's `[IsSeparated X.hom] [Flat X.hom] [LocallyOfFinitePresentation X.hom]
  [QuasiCompact X.hom]` give separated, flat and finite presentation. The usual
  additional quasi-separated clause follows from separatedness, so this excludes
  no finitely presented separated scheme and admits no extra one.
- `n : ℕ`, `V : Fin n → Over S`, `j : ∀ i, V i ⟶ X`, and `hopen` exhibit the
  finitely many open subschemes; `hcover` is their joint surjectivity onto X.
  `[∀ i, ModObj G (V i)] [∀ i, IsModHom G (j i)]` give precisely the restricted
  actions and invariance, since the open immersion is a monomorphism. They
  impose no additional action choice on X: the restricted action is unique.
- `htrans` is `Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
  (yoneda.map (ModObj.leftSMul G (V i)))`. Mathlib's `leftSMul` is exactly
  `(g,x) ↦ (g•x,x)` in the cartesian monoidal slice category, so the domain and
  codomain are the indicated fibre products. Local surjectivity of the
  represented presheaf map is surjectivity as an fppf sheaf morphism: representables
  are fppf sheaves, and this predicate says every target section lifts on a
  covering sieve. No stronger pointwise lifting or flatness of the relation
  morphism is required.
- The existential `L`, `Field L`, `Algebra K L`, `FiniteDimensional K L` is the
  finite field extension. `Algebra R L` and `IsScalarTower R K L` specify its
  compatible R-algebra structure, uniquely induced from R -> K -> L.
- Every occurrence of R' is the actual `integralClosure R L`; its carrier is
  `{a : L | IsIntegral R a}` in Mathlib, exactly the monic-polynomial construction.
  No R' is chosen from a mere existence statement. The five following conjuncts
  assert Noetherian, domain, integrally closed, dimension one, and finitely many
  maximal ideals for that very ring. T is its spectrum.
- `H Y : Over (Spec (.of (integralClosure R L)))`, the existential `GrpObj H`
  and `ModObj H Y`, give an actual T-group and its action on Y. The H clauses
  `Smooth`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` express all
  required morphism properties. The universal `Ω`, `[Field Ω]`, `t` followed by
  `ConnectedSpace (pullback H.hom t)` is exactly the node's connectedness over
  every field-valued base map, including non-algebraically-closed fields.
- The four corresponding Y conjuncts express smooth, separated, finite type.
- `f : Y ⟶ (Over.pullback (Spec.map ...)).obj X` is the T-morphism to X_T.
  Its underlying arrow followed by `pullback.fst` is precisely q:Y -> X.
  `IsIntegralHom`, `Surjective`, and `∀ x, Finite (q ⁻¹' {x})` assert the three
  required properties of q, with no extra finite-morphism conclusion.
- For every algebraically closed Ω and every `t : Spec Ω ⟶ T`, the final clause
  supplies `m : ℕ` and `U : Fin m → (pullback Y.hom t).Opens`. Their supremum
  is top and `Pairwise ... Disjoint` gives a finite disjoint open covering.
  For every algebraically closed Ω-algebra field E, the first nested clause
  says each piece is preserved by H(E). The second says any two E-valued points
  in a piece are related by some g in H(E). Points are morphisms over T;
  `pullback.lift x.left (Spec.map (algebraMap Ω E)) x.w` is their actual lift
  to Y_Ω, and its value at the field's unique `closedPoint` tests membership.
  The existing `CategoryTheory.Hom.mulAction` gives `g • x`, using the specified
  scheme action rather than an independently supplied abstract action.
  Stability plus pairwise transitivity says exactly that each nonempty piece
  is one geometric orbit. Empty pieces are harmless and may be omitted.

Dependency declarations used, with their recorded modules/interfaces:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`; `def-weil-affine-spectrum`: the same module, `Spec`, `Spec.map`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; `def-weil-pbc-normal-ring`:
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`,
  together with `IsDomain` (normal-domain clause of the dependency).
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`, together with `QuasiCompact` from its QuasiCompact module.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Flat`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `IsClosedImmersion`, used through `IsSeparated`'s closed diagonal, whose defining
  module is publicly imported.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`, and `pullback.lift`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `LocallyOfFinitePresentation`.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`, with `.over S` from
  `Mathlib.CategoryTheory.Sites.Over`.
- `def-weil-connected-scheme`: its `mathlib_match` `ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`, applied to the underlying fibre space.
- `def-weil-finite-integral-morphism`: `IsIntegralHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Integral` is the required integral clause;
  the recorded Finite module is also imported for the proof plan.

The full signatures and docstrings of these declarations were read in the pinned
local Mathlib source, as were `GrpObj`, `ModObj`, `IsModHom`, `ModObj.leftSMul`,
`Hom.mulAction`, `Over.pullback` and the slice cartesian product implementation.
No unusable dependency was found. Standard notions are used directly, not copied.
No independent missing notion required a new definition node.

Every currently stated proof dependency's module is imported (publicly when also
needed by the statement, plainly otherwise). The four proof-only nodes with
neither a `lean` record nor a `mathlib_match` at inspection were
`lem-sfb-finite-equivariant-open-orbits`,
`lem-sfb-semitrait-potential-reduced-normalization`,
`lem-sfb-trait-normalization-group-structure`, and
`lem-sfb-smooth-group-relative-neutral-open` ; they are named in the
proof docstring and have no module available to import. These proof nodes are
not statement prerequisites. No blanket imports or parallel copies were added.

Edge cases checked before writing:

- X empty: n=0 and the cover/transitivity hypotheses are vacuous; the conclusion
  can take empty Y and m=0. H itself remains nonempty on every fibre, as a group.
- A nonempty X with some empty fibres or components supported only on the
  generic point is permitted: neither a surjective structure morphism nor
  nonempty geometric Y-fibres is required.
- Empty invariant opens and empty orbit pieces are admitted. A nonempty open
  piece of the finite-type geometric fibre has geometric points; the
  transitivity condition cannot falsely make a union of two orbits one piece.
- Transitivity over E=Ω is included via its identity algebra structure; all
  algebraically closed extensions are included too. The usual Scheme.{u}
  convention uses fields in the same universe, never an independent smaller
  universe that could make the test-field quantifiers vacuous.
- No excellence, perfectness, smoothness of the original G or X, commutativity,
  or `Module.Finite R (integralClosure R L)` appears. No finite q is asserted.
- Dimension zero base fields are excluded exactly by the node's dimension-one
  assumption. Finite L/K may have degree one or be inseparable.

Searches made:

- `msearch.py ... leanfinder` query: "An almost homogeneous scheme over a
  semilocal Dedekind domain admits a potentially smooth integral cover with
  finite fibres". Eight hits, including `Algebra.Smooth.exists_finiteType`,
  `AlgebraicGeometry.IsIntegral`, and normalization/smoothness results; no match.
- `msearch.py ... loogle` query: "GrpObj, Action, IsIntegralHom". Zero hits
  (server did not recognize unqualified GrpObj); qualified Mathlib definitions
  were subsequently located and read directly using rg.
- `msearch.py ... grep` query: `almostHomogeneous|potentialSmooth|MonObj.Act|class.*MulAction`
  in AlgebraicGeometry. Zero hits.
- `msearch.py ... leansearch` query: "An almost homogeneous scheme over a
  Dedekind domain admits an integral surjective potentially smooth cover with
  finite fibres". Eight hits, including smoothness constructors, integral
  morphism definitions and scheme covers; none states this result.
- Direct `rg` of Mathlib, `lean/WeilConjectures`, `lean/Sheaf`,
  `dag/lean_names_upstream.json`, and the item id in upstream: no duplicate
  potential-smooth-cover statement. Group-action search located Mathlib's
  `ModObj` and `ModObj.leftSMul`; geometric orbit search located
  `SmoothGroupOrbitGeometry` and `HomogeneousOrbitQuotientGeometry`, whose
  declarations concern field-level orbits, not this normalization theorem.
- DAG search for group actions, invariant opens and almost homogeneity found
  no duplicate of this theorem. Standard group-scheme/action interfaces are
  already in Mathlib, so no new definitions were introduced.

Validation: `scompile.py Q71 lem-sfb-almost-homogeneous-potential-smooth-cover` passed
both sandbox and module-name compilation with no errors or unexpected warnings.
The initial probe exposed ambiguous category inference for `ConnectedSpace
(pullback H.hom t)`; adding `(C := Scheme.{u})` repaired it. The same category
annotation was added to the Y-fibre opens for clarity. The delivered node signature
was regenerated verbatim from the final source. The prescribed `deliver2.py --no-push` dry run passed server preflight and
compilation (dry-run commit `6b6cc4706db`). The only changed field of the existing
node is `lean`; its signature matches the source verbatim.
No STATEMENT-DISPUTED flag or node fault remains.

## Second reading by Q71

Independent second reading (maintainer review of delivery 1788e820; the delivered
section was the worker's own reread, replaced here). Node read clause by clause
against `exists_almostHomogeneous_potential_smooth_cover`; dependency records and
Mathlib declarations (`ModObj.leftSMul`, `Hom.mulAction`, `GrpObj`, `IsModHom`,
`Scheme.fppfTopology` + `GrothendieckTopology.over`) opened and read.

Hypotheses:
- R Noetherian integrally closed domain, dim 1, finitely many maximal ideals:
  `[IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]`, `ringKrullDim R = 1`,
  `Finite {m // m.IsMaximal}` (def-weil-pbc-normal-ring records the normal-domain
  form `IsDomain ∧ IsIntegrallyClosed`). K = Frac R by `IsFractionRing R K`. OK.
- G separated flat finite type: `IsSeparated`, `Flat`, `LocallyOfFiniteType`,
  `QuasiCompact` (finite type = LFT ∧ QC per def-weil-finite-type-morphism). OK.
- X separated flat finite presentation: LFP ∧ QC, quasi-separation implied by
  `IsSeparated` (def-sbc-locally-finite-presentation comparison clause). OK.
- Group scheme and action: `GrpObj G`, `ModObj G X` in the cartesian slice
  `Over (Spec R)` (products = fibre products over S); the node defines group
  schemes inline, and def-sc-group-scheme (over a field) records the same GrpObj.
- Finite union of invariant opens: `n`, `V`, `j`, `hopen`, `hcover`, with
  `ModObj G (V i)` and `IsModHom G (j i)`; j mono, so the restricted action is
  unique. OK.
- fppf surjectivity of (g,x) ↦ (gx,x): `ModObj.leftSMul M X := lift γ[M,X] (snd)`
  (Mathlib Cartesian/Mod.lean:91) is exactly this map G ×_S V → V ×_S V; local
  surjectivity of the represented map for `fppfTopology.over S` = epimorphism of
  fppf sheaves (representables are fppf sheaves). Not stronger. OK.

Conclusion:
- L/K finite (`FiniteDimensional K L`, `IsScalarTower R K L`), R' =
  `integralClosure R L` (the actual integral closure, not a chosen ring); its five
  ring properties stated. OK.
- H, Y over T = Spec R' with existential `GrpObj H`, `ModObj H Y`; H and Y smooth,
  separated, LFT, QC. Geometric connectedness: for every field Ω (Type u) and every
  t : Spec Ω → T, `ConnectedSpace (pullback H.hom t)`; nonemptiness is automatic
  from the identity section, so no false clause. OK.
- f : Y ⟶ X ×_S T in Over T, q = f.left ≫ pullback.fst: `IsIntegralHom`,
  `Surjective`, finite fibres `Finite (q ⁻¹' {x})`; no finiteness of q or of R'/R. OK.
- Orbits: for algebraically closed Ω and t, finitely many pairwise disjoint opens
  U i covering Y_Ω; for every algebraically closed Ω-field E, U i is stable under
  H(E) and any two E-points in U i are related by some g ∈ H(E) (`g • x` is
  Mathlib's `Hom.mulAction` from the given action). E-points are lifted to Y_Ω
  through Spec E → Spec Ω and tested at the closed point. Each nonempty U i is
  thus exactly one geometric H_Ω-orbit; empty pieces allowed as the node says. OK.

Edge cases: empty X (n = 0, Y empty, m = 0); empty fibres and generic-only pieces;
E = Ω via `Algebra.id`; degree-one or inseparable L; Type-u test fields (the
size convention, residue-field closures live in Type u). No extra assumption.

One definition per notion: DAG definition nodes on group schemes/actions searched
(def-sc-group-scheme = GrpObj; def-sfb-scheme-action-torsor-groupoids builds
groupoids over a given action, not a competing action notion;
def-wf-algebraic-components is over a field and not used in the statement). No
duplicate of the theorem in Mathlib, lean/WeilConjectures or lean/Sheaf.

Records: node changes only `lean`; `lean.statement` equals the source signature
verbatim; module and declaration docstrings carry the source place and
`(blueprint: …)`, the declaration docstring the ten proof steps; proof `sorry`;
no definitions. No mismatch found; no Lean change.
