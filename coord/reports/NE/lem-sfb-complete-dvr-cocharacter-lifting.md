## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.CompleteDvrCocharacterLifting states
AlgebraicGeometry.RingGroupSchemes.completeDvr_cocharacter_lifting with a sorry proof.
It introduces no definitions. The node's mathematical statement is unchanged.
The only additional statement dependency is the already landed
`def-sfb-split-torus-over-ring`, whose multiplicative group is used directly.

Hypothesis and conclusion correspondence:

- A discrete valuation ring: `(A : Type u) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]`. The last class extends local and principal-ideal
  ring and explicitly excludes fields by its nonzero maximal ideal.
- A uniformizer π: `(π : A) (hπ : Irreducible π)`.
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies this with
  `IsLocalRing.maximalIdeal A = Ideal.span {π}` exactly.
- k = A/(π): every special-fibre pullback is along
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π})))`.
  Thus k is the actual quotient, not an independent field or a chosen ring map.
  It is a field because π generates the maximal ideal; its Field instance is
  unnecessary for these scheme and group constructions.
- Bijectivity of the canonical completion map: `hcomplete : Function.Bijective
  (AdicCompletion.of (Ideal.span {π}) A)`. This is the recorded module-completion
  form of the ring completion. Its nth quotient is by I^n • top = I^n = (π^n).
  Its n = 0 quotient is the zero ring, adding one uniquely determined compatible
  component to the node's system indexed by n ≥ 1, hence the same limit.
- An A-group scheme: `H : Grp (Over (Spec (.of A)))`. `Grp` bundles the recorded
  `GrpObj` group diagrams on an object of the category of schemes over Spec A.
- Smooth: `[Smooth H.X.hom]`; affine: `[IsAffineHom H.X.hom]`.
- Finite type: `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`, the exact
  conjunction specified in the finite-type dependency's record.
- G_m,A: `RingGroupSchemes.multiplicative A`, the existing Hopf spectrum of
  LaurentPolynomial A with its actual unit multiplication, identity and inverse.
- Every homomorphism lambda0 of k-group schemes: the `lambda0` binder is a
  morphism between the canonical pullbacks of this multiplicative group and H,
  under `(Over.pullback ...).mapGrp`. It therefore includes the group law
  compatibility, not merely an arbitrary morphism of schemes.
  Representing G_m,k by this pullback is its definition as special fibre:
  the Laurent algebra base changes to k[z,z⁻¹], with the same Hopf operations.
  This changes no quantifier and requires no arbitrarily chosen comparison map.
- Existence of an A-group homomorphism lambda: `∃ lambda : multiplicative A ⟶ H`.
- Its special fibre equals lambda0: `(Over.pullback ...).mapGrp.map lambda = lambda0`.
  Equality is equality of group-scheme arrows, rather than just conjugacy or
  equality on rational points.
- No reductivity, connectedness, perfection or algebraic closedness appears.

Dependency declarations read and used:

- def-sc-group-scheme: Mathlib.CategoryTheory.Monoidal.Grp,
  CategoryTheory.GrpObj and CategoryTheory.Grp. Read the full group structure
  including inverse identities and the bundled Hom constructors. The recorded
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documentation confirms
  the Over/GrpObj encoding; the generic Mathlib declaration already works over A.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  AlgebraicGeometry.Smooth, the affine-local smooth ring-map condition.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  AlgebraicGeometry.LocallyOfFiniteType, and Morphisms.QuasiCompact,
  AlgebraicGeometry.QuasiCompact. Their conjunction is finite type.
- def-sc-discrete-valuation-ring: Mathlib.RingTheory.DiscreteValuationRing.Basic,
  IsDiscreteValuationRing and IsDiscreteValuationRing.irreducible_iff_uniformizer.
- def-weil-pbc-adic-completion: Mathlib.RingTheory.AdicCompletion.Basic,
  AdicCompletion and AdicCompletion.of. Read the compatible-sequence definition,
  the canonical map, IsAdicComplete and its equivalence of_bijective_iff.
- def-sfb-split-torus-over-ring: the existing
  Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing,
  AlgebraicGeometry.RingGroupSchemes.multiplicative. Read local and live server
  source (scompile.py --source); both give exactly the Laurent Hopf spectrum.
- Canonical base change: Mathlib.CategoryTheory.Monoidal.Cartesian.Over,
  CategoryTheory.Over.pullback, and Mathlib.CategoryTheory.Monoidal.Grp,
  CategoryTheory.Functor.mapGrp (finite-product-preserving group transport).

Proof imports include the recorded Noetherian definition, affine permanence
(Affine and Separated), and finite-presentation definition. The proof dependency
lem-sfb-complete-local-split-torus-hom-lift has no Lean record or Mathlib match;
it is needed for the future proof, not to type this statement, so no import can
currently be added. The full three-step node proof is in the theorem docstring.

Edge cases checked before writing: the trivial cocharacter is allowed (no mono
condition); H may be disconnected, nonreductive, or itself trivial; imperfect
residue fields and mixed/equal characteristics are unrestricted. π = 0 and unit π
are excluded exactly by the uniformizer condition in a genuine DVR, and a field
A is excluded by the recorded DVR class. There is no rank-positive hypothesis
on H. All rings and schemes use the standard Scheme.{u} convention; all variables
and the universe u are explicit and both autoImplicit settings are false.

Searches made:

- msearch.py leanfinder, query `Lift a cocharacter of a smooth affine group scheme
  over a complete discrete valuation ring`: eight hits, headed by
  AlgebraicGeometry.ValuativeCommSq.i₁ and affine-space/valuative declarations;
  none is a group-scheme cocharacter lifting theorem.
- msearch.py loogle, query `"cocharacter"`: zero hits.
- msearch.py grep, query `cocharacter|one.parameter|Hom.*GroupScheme`: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for cocharacter, Gm,
  multiplicativeGroup, MultiplicativeGroup, groupSchemeBaseChange, and module
  file names: existing conjugacy theorems over fields and the ring-base
  SplitTorusOverRing construction; none states this lifting theorem.
- rg for the exact item id in lean/WeilConjectures: zero hits.
- DAG search for splitTorusOverRing, multiplicativeGroup, multiplicative group
  scheme and split torus over finds def-sfb-split-torus-over-ring, used here.
  No new definition node is needed.

Sources independently checked in the author-hosted PDFs:
https://sites.math.washington.edu/~jarod/papers/iwahori.pdf (Lemma 3.6 and §4),
https://math.stanford.edu/~conrad/papers/luminysga3.pdf (Corollary B.3.5,
printed p.292). Conrad states exact lifting from the special fibre for a smooth
 affine target over a complete local Noetherian ring, with no reductivity or
residue-field assumptions. This confirms the node's rank-one specialization.
No STATEMENT-DISPUTED flag or mathematical node correction is needed.

Validation: scompile.py compiled the delivered module cleanly in sandbox and
library module modes (15.1 seconds and 6.4 seconds). No diagnostics were printed.

## Second reading by NE

The dispatcher prohibits starting other agents; this is a second pass by the
same worker, not a claim of independent review. The maintainer supplies the
independent review after delivery. Reopened the node and final module and
checked all binders and the conclusion against the correspondence above.
Confirmed that lambda0 is on the actual canonical special fibre, that lambda
is a bundled group morphism, and that the asserted equality is exact.
The source is the existing ring-base Laurent group, not the field-only
StandardGroupSchemes construction. Completeness is bijectivity, and the
uniformizer is the dependency's equivalent irreducibility formulation.
No additional assumptions and no missing clauses were found. No theorem is
proved, no construction uses sorry, and no dependency interface needs repair.
