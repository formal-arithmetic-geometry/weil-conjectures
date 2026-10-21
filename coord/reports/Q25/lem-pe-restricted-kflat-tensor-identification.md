## Worker report

The module `Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification` states the
node using its published cochain derived-change-of-rings interface. All six theorem
proofs are `sorry`. Definitions have real data; the model structure records the
specified objects and maps together with their characterizing equations. No node
statement, dependency interface, or dependency list is changed.

Source read: `sites-cohomology.tex`, lemma-derived-base-change (06YY) and
lemma-derived-tor-quasi-isomorphism-other-side (06YT); `sites-modules.tex`,
section-tensor-product (03EK) and lemma-sheafification-presheaf-modules (03CY).
The swap and arbitrary-linear coefficient clauses are the node's explicit
refinement of these constructions, rather than a claim that 06YY prints this square.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`,
  `[EssentiallySmall.{r} C]`. Ring sheaves have coefficient universe `r`.
  The sheaf-compose, locally-bijective, and sheafification instances supply the
  ordinary module-sheaf and abelian structures on that site. Site object and Hom
  universes and the four derived localization universes remain independent.
- `B A S : Sheaf J CommRingCat.{r}`, `u : B ⟶ A`, and `v : A ⟶ S` are the two ring
  morphisms; their composite is literally `u ≫ v`. The further ring is `T` and its
  map is `w : A ⟶ T`.
- Module sheaves are `ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)`,
  transparently Mathlib `SheafOfModules` on the underlying ring sheaf.
- Unbounded complexes are `CochainComplex ... ℤ`; `DerivedCategory` and
  `DerivedCategory.Q` are the recorded localization, with independently selected
  `HasDerivedCategory` structures, with no boundedness predicate.
- `restrictedTensorScalars` is only a transparent abbreviation of the dependency's
  `SheafOfModules.restrictScalars`. Its named finite-limit and finite-colimit
  theorems express exactness from proof step 1; `restrictedTensorScalars_quasiIso`
  states the quasi-isomorphism preservation clause directly.
- The induced derived restriction is Mathlib's `.mapDerivedCategory`. The canonical
  `restrictedTensorLocalization` is `.mapDerivedCategoryFactors.symm`, a natural
  isomorphism with source `Q_A Res_v` and target `Res_v Q_S`. Consequently compatibility
  with every cochain map is part of the actual type, not an omitted property.
  `restrictedTensorLocalization_commShift` states `NatTrans.CommShift` of its hom;
  the termwise and derived restriction use the canonical Mathlib shift structures.
- The represented object and representation are `K`, `G`, and `e : Q.obj G ≅ K`.
  The chosen resolution is `f : P ⟶ G` with `[QuasiIso f]` and
  `hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P`.
  `hflat : ∀ n : ℤ, IsFlatOnSite (R := B) (P.X n)` states flatness of every term.
  These are exactly the two conjuncts of the dependency's K-flat-resolution
  predicate, together with the node's flat-terms condition.
- `D : DerivedChangeOfRingsCochainModel (u ≫ v)` is an arbitrary presentation of the
  recorded derived extension, including its universal counit. It is mathematical
  interface data, not a replacement assumption: the dependency's existence theorem
  supplies it for every ring map. `D.E.obj_eq` and `D.E.map_eq` identify the ordinary
  extension and its differential with sheafification of `S tensor_B P` and
  `1 tensor d_P`, with the S action on the first factor. `restrictedTensorFirstSection`
  explicitly transports the sheafification-unit image of `s tensor p` using `obj_eq`.
- `RestrictedKFlatTensorIdentification.H` is the S-linear scalar-last complex.
  Its `last` is a B-linear cochain isomorphism to the existing
  `restrictedTensorLastComplex (u ≫ v) P`, namely the termwise functor
  `siteSheafTensorRight (restrictedTensorCoefficient (u ≫ v))` applied to P.
  This is the actual sheafification of `P tensor_B S` with `d_P tensor 1`.
  It does not substitute an unconstrained complex for the scalar-last tensor.
- `τ` is an S-linear cochain isomorphism from the scalar-first complex to H.
  `swap` requires its B-linear realization on every section in every degree to send
  the original pure tensor `s tensor p` to `siteSheafTensorTmul ... p s`.
  These original local sections generate after sheafification, so this pins down
  the entire comparison; its inverse sends `p tensor s` to `s tensor p`.
  S-linearity and this equation also pin down the S-action on H as the last-factor
  coefficient action. The `last` identification preserves differentials.
- `c` is `F(QG) ≅ QH`. Its `computation` equation says that, after undoing τ,
  it is `inv (F.map (Q.map f)) ≫ D.ε.app P`. This is precisely the canonical
  K-flat computation map, not an arbitrary isomorphism with that source and target.
- `η` has the stated type `F K ≅ QH`; `eta_eq` is exactly
  `D.T.mapIso e.symm ≪≫ c`. `δ` has source `Q_A(Res_v C_S)` and target
  `Res_v(F K)`. `delta_eq` is literally localization of restricted τ, then λ,
  then derived restriction of η inverse. Its `Iso` type supplies the asserted
  inverse. The existence theorem supplies all this data for every specified resolution.
- The coefficient theorem uses the same P, G, e, f for DS and DT and for dS and dT.
  Its `h` is a morphism between the restricted coefficient **module sheaves** over A;
  it has no ring-map, multiplicativity, or unit-preservation hypothesis.
- The existential `a` and `b` are A-linear cochain maps on the scalar-first and
  scalar-last representatives. The first conjunct specifies `a(s tensor p) =
  h(s) tensor p` via the actual sheafification unit. The second conjunct, in the
  `last` coordinate on H, specifies `b(p tensor s) = p tensor h(s)`.
- The third conjunct is exactly the cochain swap square, written in Lean's order
  of composition: `a ≫ Res_w τ_T = Res_v τ_S ≫ b`.
- The fourth conjunct is the derived identification of these maps:
  `δ_S.inv ≫ Q.map a ≫ δ_T.hom` equals
  `Res_v(η_S.hom) ≫ λ_S.inv ≫ Q.map b ≫ λ_T.hom ≫ Res_w(η_T.inv)`.
  This is precisely proof step 7 in Lean's composition order, and it uses no
  putative S-linearity of h or cross-ring naturality of λ.
- There are no flatness assumptions on u, v, w, no completeness assumption, and no
  boundedness assumption. The only flatness assumptions concern the terms of P.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` (also publicly imported by the cochain model).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the recorded tensor interface and its imports `siteSheafTensorRight`,
  `siteSheafTensorTmul`; its independent-site tensor structures remain the existing ones.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`; exact restriction
  uses `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and its
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, and canonical shifts.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` and its additive instance.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and the resolution predicate read
  there; this module is publicly imported by the derived model.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`.
- Proof imports: `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`,
  `sheafRingCoefficientOrdinaryAdjunction`; Mathlib presheaf-module sheafification
  and its universal property. Ordinary tensor extension is the published
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct` construction.

Edge cases checked: zero rings and zero modules (all tensor formulas still type);
empty site (no nonemptiness assumption); zero complex and arbitrary unbounded
complexes; degree zero and negative degrees; identity ring maps; h the identity,
h the zero map (including a nonunital map on a nonzero coefficient ring), and
multiplication by an A-scalar (generally not a ring map). There is no sign in the
swap, since the coefficient is in degree zero. Only P itself is required to be
K-flat; no restriction of P is claimed K-flat. Distinct site universes and distinct
derived morphism universes compile without imposed equalities.

Searches actually run:

- `msearch.py leanfinder`, query `K flat derived scalar extension sheaves restriction
  scalars scalar first tensor swap natural arbitrary linear coefficient map`: eight
  hits, including `ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat`,
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`, and the ordinary
  extend/restrict Hom equivalence; none is the derived sheaf swap statement.
- `msearch.py loogle`, query `SheafOfModules.restrictScalars,
  Functor.mapDerivedCategory, tensor`: zero hits; the service reports unknown
  identifier `Functor.mapDerivedCategory`. This is a search-parser/name limitation,
  not evidence that the declaration is absent; its full Mathlib source was read.
- `msearch.py grep`, query `restrictScalars|changeOfRings|tensor`, directory
  `Algebra/Category/ModuleCat/Sheaf`: ten reported hits, chiefly ordinary restriction
  in `ChangeOfRings.lean` and `PushforwardContinuous.lean`; no matching theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for scalarFirst/scalarLast,
  derivedRestrictScalars, tensor swap and restricted-tensor comparisons found
  ordinary `ChangeOfRingsTensorComparison` and coefficient-specific derived
  restriction. The ordinary comparison was read: it identifies restricted
  extension with scalar-first sheaf tensor and does not state this node's
  S-linear swap, K-flat comparison or arbitrary A-linear coefficient square.
- `rg` for the node id in `lean/WeilConjectures` found no implementation. Searches
  for every introduced declaration prefix in `dag/lean_names_upstream.json`,
  Mathlib, the upstream sources and `lean/Sheaf` found no collision.
- DAG search for the restricted scalar-first/scalar-last identification found this
  node and its successive-quotient consumer, not a duplicate definition node.

No statement fault or STATEMENT-DISPUTED is asserted. No new nodes or dependency
modules are required: the additional declarations are the canonical comparisons
and coordinate interface belonging to this node, as authorized by the brief.

## Second reading by Q25

Author's second reading (not an independent reviewer; this dispatcher forbids
starting another agent). Reopened the node and final module. The site universes,
B to A to S maps, unbounded derived categories, representation e, quasi-isomorphism
f, K-flatness and all flat terms match the explicit binders. Checked that lambda
has the inverse orientation of Mathlib's factor comparison, that `computation`
undoes τ on its target, and that eta composes F(e inverse) before c. Checked delta's
source and target against all three arrows in the node. Checked h is solely an
A-module morphism and both a and b live in A-complexes. Compared the last displayed
identity with proof step 7: Lean composes left to right, hence the delta inverses
and eta directions match after reversing the paper's notation. The scalar-last
realization uses the existing sheaf tensor in order P then S; the explicit `swap`
equation prevents an arbitrary isomorphism or an arbitrary action on H. The first
compile identified the missing `[QuasiIso f]` on the model structure needed to type
the inverse of F(Q f); it was added, matching the already-stated resolution
hypothesis. No mathematical statement was changed.
