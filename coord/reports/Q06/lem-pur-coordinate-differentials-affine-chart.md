## Worker report

The module `Sheaf.AlgebraicGeometry.CoordinateDifferentialsAffineChart` states
`AlgebraicGeometry.Scheme.exists_coordinate_differentials_affine_chart`, with exactly one
postponed theorem and no proofs supplied. Its auxiliary definition
`AlgebraicGeometry.Scheme.HasCoordinateDifferentialAffineChart` expands the entire conclusion
while installing the canonical scalar structures locally inside the definition. Its body is
an explicit proposition, without `sorry`, choices of unknown objects, or extra hypotheses.
Both declarations belong to this item and are listed in `lean.declarations`.

The natural-language statement, its dependencies and its proof are unchanged. There are no
new nodes, dependency repairs, statement disputes or corrections. Read the current blueprint
`sec-smooth-purity/sk-prop-an/lem-pur-regular-immersion-linearization.proof.md`, second paragraph,
and the source labels in Stacks `morphisms.tex` (01V7 and 02GU(8)), `algebra.tex` (00T7(2)).
The current example `Sheaf.CategoryTheory.CompactObject` has been withdrawn; its recorded
upstream definition is the convention reference, not an import needed here.

Hypothesis-by-hypothesis correspondence:

- A field: `(k : Type u) [Field k]`, with no perfectness, characteristic or algebraic-closure
  hypothesis.
- A k-scheme: `(U : Scheme.{u}) [U.Over (Spec (.of k))]`; its structure morphism is
  `U ↘ Spec (.of k)`.
- Finite type: `[LocallyOfFiniteType (U ↘ Spec (.of k))]` and
  `[QuasiCompact (U ↘ Spec (.of k))]`, exactly the recorded conjunction.
- Smoothness: `[Smooth (U ↘ Spec (.of k))]`.
- A point, nonnegative integer, and global functions: `(x : U) (d : ℕ)` and
  `(h : Fin d → Γ(U, ⊤))`.
- The prescribed differential classes form a residue-field basis: `hbasis` supplies a
  `Module.Basis (Fin d)` whose value at every `j` is `1 ⊗ germ_x(d(h j))`. A basis is exactly
  a linearly independent spanning family. The module is the residue-field extension of
  the recorded `RingedSpace.moduleStalkFunctor` applied to the recorded relative
  differential sheaf. The scalar field `IsLocalRing.ResidueField (U.presheaf.stalk x)` is
  definitionally the carrier of `U.residueField x`.

Clause-by-clause correspondence, after expanding the auxiliary predicate:

1. The conclusion binds `(W : U.Opens) (hW : IsAffineOpen W) (hx : x ∈ W)`.
   Thus `A = Γ(U,W)` and the canonical chart is `hW.fromSpec : Spec A ⟶ U`. The canonical
   k-algebra structure on A is the composite of `ΓSpecIso.inv`, the structure morphism's
   `appTop`, and restriction to W. This is specified data, not an existential scalar map.
2. It supplies `r : ℕ` and
   `P : Algebra.SubmersivePresentation k A (Fin (r+d)) (Fin r)` with
   `P.map = Fin.castAdd d`. Hence n is r+d, n≥r, and the selected Jacobian minor is exactly
   the first r variables. `P.relation` is the family F and `P.val` the family a. The
   `SubmersivePresentation` supplies an invertible Jacobian determinant and its underlying
   `Presentation` supplies precisely the stated quotient isomorphism α: its
   `span_range_relation_eq_ker` identifies the relation ideal with the evaluation kernel,
   and `P.toPresentation.quotientEquiv.restrictScalars k` is α after that identification.
   Its defining formula sends each variable class to `P.val`. No weaker assertion of
   abstract standard smoothness replaces the presentation.
3. The prime corresponding to x is exactly `(hW.primeIdealOf ⟨x,hx⟩).asIdeal`.
   The existential `ε` is a ring equivalence from its `Ideal.ResidueField` to K, required
   to send every residue of `a : A` to `(U.residue x) (germ a)`. This characterizes the
   canonical identification: residues and inverses generate the residue field. The
   canonical A-algebra on K is installed via that same germ followed by residue.
4. The map `g : KaehlerDifferential k A →ₗ[A]` the differential stalk is required, for
   every a in A, to send `D a` to `germ_x(d a)`. These generators determine g uniquely.
   Its A-module codomain uses restriction of scalars along the actual germ homomorphism.
   `Φ` is a K-linear equivalence from `K ⊗[A] Ω[A/k]` to the sheaf cotangent fibre and is
   required on every pure tensor to satisfy `Φ(c ⊗ ω) = c ⊗ g ω`. This is the asserted
   canonical formula on all ω, not only on a chosen basis. Tensor factors are reversed
   from the node using the canonical commutativity identification, as prescribed by the
   recorded module-base-change node. A separate clause explicitly gives its value on
   every `D(res(h j))`, namely the originally specified global differential class.
5. A basis `b : Module.Basis (Fin d) K (K ⊗[A] Ω[A/k])` is required to take j to
   `1 ⊗ D(P.val (Fin.natAdd r j))`. These are precisely the last d variable differentials.
6. The family `H : Fin d → MvPolynomial (Fin (r+d)) k` satisfies
   `MvPolynomial.aeval P.val (H j) = res(h j)` for every j.
7. R is `MvPolynomial (ULift.{u} (Fin d)) k`; its action on A is explicitly evaluation
   at the restricted h's. The universe lift is the bijective reindexing required for
   Mathlib's d-dimensional affine space, and changes no algebra or coordinate family.
   `G : Algebra.Presentation R A (Fin (r+d)) (Fin r ⊕ Fin d)` has `G.val = P.val`.
   Its `Sum.inl` relations are exactly the coefficient extensions of F; its `Sum.inr`
   relations are exactly the coefficient extensions of H minus the constant polynomial
   with coefficient `X (ULift.up j)`. As with P, the relation-span/kernel equality and
   `G.quotientEquiv.restrictScalars R` encode the displayed R-algebra quotient isomorphism,
   sending each y variable to a. This is full presentation data, not just a surjective
   map or the vanishing of the displayed relations.
8. The last equality identifies `Spec.map` of that evaluation homomorphism, followed by
   `(AffineSpace.SpecIso ...).inv`, with `hW.fromSpec` followed by the global
   `AffineSpace.homOfVector` determined by h. This states exactly that the resulting
   R-algebra structure gives the restriction of the prescribed k-morphism to W.

Dependency declarations used (full signatures and source docstrings read):

- `Field` in `Mathlib.Algebra.Field.Defs`; `Scheme.Over` in
  `Mathlib.AlgebraicGeometry.Over`; `LocallyOfFiniteType` and `QuasiCompact` in their
  recorded `Mathlib.AlgebraicGeometry.Morphisms` modules; `Smooth` in the recorded
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `Scheme.Hom.relativeDifferentials` and `relativeDifferentialsDerivation` in
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`; the affine and restriction
  comparison declarations in that module supply the proof plan's canonical affine
  description. No differential sheaf is redefined.
- `RingedSpace.moduleStalkFunctor` in
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor` supplies the actual stalk module;
  raw presheaf germs appear only to describe elements of this same carrier.
- `Scheme.residueField` and `Scheme.residue` in `Mathlib.AlgebraicGeometry.ResidueField`;
  `Localization.AtPrime` in `Mathlib.RingTheory.Localization.AtPrime.Basic` and the
  existing `Ideal.ResidueField` identify κ(q) with the residue field of A_q.
- `TensorProduct` and extension-of-scalars conventions of `LinearMap.baseChange` in
  `Mathlib.LinearAlgebra.TensorProduct.Tower`.
- `Spec`, `Spec.map`, and `Scheme.ΓSpecIso` in `Mathlib.AlgebraicGeometry.Scheme`;
  `IsAffineOpen.primeIdealOf` and `fromSpec` in `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Algebra.IsStandardSmooth` in `Mathlib.RingTheory.Smooth.StandardSmooth` and its recorded
  presentation data `Algebra.SubmersivePresentation` in
  `Mathlib.RingTheory.Extension.Presentation.Submersive`; the inherited `Presentation`
  and its `quotientEquiv` come from `Mathlib.RingTheory.Extension.Presentation.Basic`.
- `KaehlerDifferential`, `KaehlerDifferential.D` in `Mathlib.RingTheory.Kaehler.Basic`;
  `MvPolynomial`, `MvPolynomial.aeval` and its universal property in
  `Mathlib.Algebra.MvPolynomial.Basic`/`Eval`.
- `AffineSpace`, `AffineSpace.SpecIso`, `AffineSpace.homOfVector` in
  `Mathlib.AlgebraicGeometry.AffineSpace` use the recorded coordinate-index convention.
- Proof-only dependencies are imported non-publicly: `SubmersivePresentation.basisKaehler`
  in `Mathlib.RingTheory.Smooth.StandardSmoothCotangent`, `tilde.toStalk` and its
  `IsLocalizedModule` instance in `Mathlib.AlgebraicGeometry.Modules.Tilde`, and
  `invariantBasisNumber_of_nontrivial_of_commRing` in
  `Mathlib.LinearAlgebra.InvariantBasisNumber`. The other proof dependencies are supplied
  by the statement imports: `Smooth.exists_isStandardSmooth`,
  `IsAffineOpen.isLocalization_stalk`, `fromSpec_app_self`, `fromSpec_primeIdealOf`, and
  `Scheme.ΓSpecIso_naturality`. There is no omitted available proof-dependency module.

Edge cases checked before writing: d=0 gives an empty input family, last-variable basis and
H family; the graph presentation then just extends the original relations over the
zero-variable polynomial ring. For r=0 the standard-smooth minor is the empty determinant
one, and the graph relations are exactly H_j−T_j. The case r=d=0 is permitted. The selected
point excludes an empty affine chart; an empty U makes the quantified hypothesis x
uninhabited. No rational-point, closed-point, separability or perfectness assumption was
introduced: K and κ(q) can be arbitrary residue extensions. All universes and variables are
explicit; no equality of unrelated universes is imposed. Canonical ULift reindexing includes
u=0 and empty coordinate types.

Searches for reuse, executed through msearch.py:

- LeanFinder: "Smooth scheme affine chart cotangent fibre basis and polynomial graph
  presentation for prescribed functions" returned `SubmersivePresentation.basisCotangent`,
  `Generators.exists_presentation_of_basis_cotangent`, related basis results and
  `exists_presentation_of_free_cotangent`; none states this geometric chart, canonical
  fibre comparison and prescribed graph presentation together.
- Loogle: "Algebra.SubmersivePresentation, KaehlerDifferential" returned eleven results
  including `basisKaehler`, `basisKaehlerOfIsCompl`, `rank_kaehlerDifferential` and
  `free_kaehlerDifferential`. These supply the algebraic proof input, not the whole node.
- Mathlib grep: "exists_isStandardSmooth|relativeDifferentialsSpecIso|basisKaehler"
  returned the smooth-chart existence lemmas, standard-smooth basis results and
  standard-smoothness criteria; no exact full-statement match.
- LeanSearch: "Affine standard smooth chart canonical cotangent fibre isomorphism and
  graph presentation of prescribed functions" returned unrelated manifold charts and
  algebraic cotangent-equivalence facts, and the general smoothness recursor; no match.
- Direct rg over `lean/WeilConjectures` and `lean/Sheaf` for relative differentials and
  coordinate/graph chart terms found and reused the upstream differential construction.
  The parent `EtaleAtPointFromDifferentials` states the eventual étaleness conclusion,
  not this chart statement. `RelativeDifferentialsAffineSections` is only the affine
  differential-sheaf comparison, also not this statement. No second construction used.
- Direct grep of the item id in `lean/WeilConjectures` returned no hits. Direct rg of
  both new fully qualified name suffixes in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`
  and `dag/lean_names_upstream.json` returned no hits.

Validation: scompile.py compiled this single delivered module against the live server
library in sandbox and library modes, cleanly (5.9 s and 3.9 s). Diagnostic failures during
writing were repaired: the reserved lambda token was renamed, the final coordinate
index was projected with `.down`, and the germ tensor's recorded stalk-module carrier
was specified explicitly. The final module has no diagnostic commands or non-sorry
warnings. The sole theorem proof is `by sorry`; every definition has real data.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
