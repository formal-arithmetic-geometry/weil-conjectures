## Worker report

Delivery: `Sheaf.Paper.FiniteTargetChangeCoherence`, main declaration
`WeilConjectures.finiteTargetChange_coherence`. The theorem has one `sorry` and the complete
five-step natural-language proof of the node in its docstring. All helper definitions have
actual bodies; the family and laws records only collect the hypotheses and conclusions of
this node. No new mathematical notion or dependency module is introduced.

Source read: main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/
cor-coef-finite-verdier.proof.md, in particular the resulting map, evaluation compatibility,
and quotient cocycle. Also read the item's five proof steps, all thirteen statement
dependencies' statements and recorded interfaces, and the finite-Hom module's declarations.
The source's dualizing target is generalized in this already reviewed node to arbitrary
compatible finite-Tor constructible targets; the Lean retains that generality.

Hypotheses and clauses:

- The fixed algebraic closure of the finite field is `D : FiniteFieldDatum.{u}`. Its fields
  carry the prime, positive exponent, finite base field and chosen algebraic closure.
- The coefficient prime is `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`. The finite extension
  is `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]`. Every quotient is the dependency's
  `Padic.coefficientExtensionRing l E (n + 1)`, using its chosen uniformizer.
- The separated finite-type k-scheme is `X : Scheme.{u}`, `[X.Over (Spec (.of D.k))]`,
  `[IsSeparated (X ↘ Spec (.of D.k))]`, `[LocallyOfFiniteType ...]`, `[QuasiCompact ...]`.
  There is no properness assumption on X. The Proper module exposes the dependency's
  separatedness class; it is not used to impose properness.
- The node fixes either site. The conclusion is the conjunction of the etale and intrinsic
  pro-etale instances of `FiniteTargetChangeLaws`, so it supplies precisely the same claim
  on each. The etale category is `finiteHomEtale`, the ordinary small-etale
  `Etale.DerivedCategoryModule` with the canonical ULift of the coefficient ring. The
  pro-etale category is `normalizedDVRDerived`, definitionally the recorded intrinsic
  `proEtaleDerivedCategory` with its standard localization. Both are the ordinary module
  derived categories used in `thm-coef-finite-hom`, with their actual universes retained.
- The two `P` arguments are exactly `finiteTorConstructibleEtale` and
  `finiteTorConstructible`. They reuse finite-value bounded constructibility on the etale
  site, intrinsic finite-torsion constructibility on the pro-etale site, and a single finite
  Tor interval tested against every degree-zero module sheaf. No site-perfect restriction
  or flatness of a quotient is added.
- `N : ℕ`, `_hN : 1 ≤ N` is the length. `FiniteTargetChangeFamily.obj` is indexed by
  `Fin N`. An index with value n means positive exponent n+1. This bijects exactly with
  the levels 1 through N and introduces no level zero or levels above N.
- `FiniteTargetChangeFamily.constructible` says each Omega is in the specified ctf domain.
  `transition` is an actual isomorphism from `(F h).obj (obj i)` to `obj j` for every
  ordered pair. `unit` identifies the diagonal transition with the canonical scalar unit;
  `cocycle` uses `α.hom.app (obj i)` before the direct transition, so both sides have the
  common source `S_jr(S_ij Omega_i)`.
- The Hom bifunctors are the dependency's `finiteHomEtaleInternalHom` and
  `coefficientFiniteInternalHom`. Their tensor-Hom counits are supplied by the same
  normalized closed structures used to define `v` in the finite-Hom theorem.
- `finiteTargetChangeArrow` is the definition in the node: `S.comparison h K (Ω.obj i)`
  followed by `(H j).map (Prod.mkHom (𝟙 _) (Ω.transition i j h).hom)`. Its body does not
  choose a map or substitute a comparison known only to exist.
- `FiniteTargetChangeLaws.isIso` states invertibility for every ctf K and every family.
  `naturality` is the contravariant square for each morphism `f : K ⟶ L` between ctf
  objects. The first-variable maps are `f.op` and `((F h).map f).op`, in the appropriate
  directions. Naturality and componentwise invertibility express natural isomorphisms
  on the full ctf subcategories without choosing inverses before their theorem is proved.
- `evaluation` says `(h ⊗ 1) ≫ ev = μ.inv ≫ F(ev) ≫ u`. The inverse tensor comparison
  has source `F(H_i(K,Omega_i)) ⊗ F(K)`, exactly the identification suppressed in the TeX.
- `cocycle` is `α_H ≫ h_ir = F_jr(h_ij) ≫ h_jr ≫ H_r(α_K.inv,1)`.
  Thus it identifies the Hom source by the scalar associator and the first Hom input by
  its inverse, leaving Omega_r unchanged. These are precisely the canonical scalar
  identifications implicit in the node's displayed equality.
- `unit` is `h_ii ≫ H_i(ε_K.inv,1) = ε_H`. Under the canonical scalar unit both sides
  identify with the identity of H_i(K,Omega_i), which renders h_ii=1 without pretending
  scalar extension is definitionally the identity functor.
- `target_naturality` quantifies over arbitrary maps `t i : Ω.obj i ⟶ Ω'.obj i` satisfying
  `(Ω.transition ...).hom ≫ t j = F.map (t i) ≫ (Ω'.transition ...).hom` and gives exactly
  `h_Ω ≫ H(1,t_j) = F(H(1,t_i)) ≫ h_Ω'`. No `IsIso` is imposed on t.
- Neither the target family nor any conclusion mentions dualizing objects.

Dependency declarations used (their modules are publicly imported):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: exposes the coefficient rings,
  uniformizer and ideals, and `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...Proper`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: ordinary
  `Etale.DerivedCategoryModule` and cohomological conventions.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `ProEtale.FiniteCoefficientModules`,
  finite coefficient ring sheaf and comparison presentation; used through the intrinsic
  finite-level presentation in the recorded finite-Hom arrows.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale`,
  `finiteTorConstructible`, with their recorded Tor and constructibility definitions.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: the generic universal
  change-of-rings interface. Its finite specializations here are the finite-Hom module's
  `finiteHomEtaleReduction` and `coefficientFiniteQuotientDerived`, not new functors.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: generic ringed-site Hom and
  exposed `Etale.derivedHom`; specialized here by the dependency's Hom bifunctors.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`: `basicOperationsCoefficientReduction`
  and the canonical tensor/reduction convention from the existing statement dependency.
- `Sheaf.Paper.FiniteCoefficientHomChange`: `FiniteHomQuotientClosedData`, its
  `.comparison`, `finiteHomEtaleData`, `finiteHomEtaleAssoc`, `finiteHomIntrinsicAssoc`,
  `finiteIntrinsicClosed`, `coefficientFiniteInternalHom`, and
  `finiteCoefficient_derivedHom_change`. The intrinsic shared-data wrapper retains the
  exact closed and quotient tensor fields used by that theorem, so its comparison unfolds
  to `proEtaleFiniteHomCanonical`; the etale comparison unfolds to
  `etaleFiniteHomCanonical`.
- `Sheaf.Paper.NormalizedOriginScalarComparisons`:
  `ProEtale.normalizedOriginScalarUnit`, applied to `RingHom.ulift` of
  `Ideal.Quotient.factor_eq`. This existing node
  `def-weil-pbc-normalized-origin-scalar-comparisons` is added to stmt_deps to record the
  extra direct dependency. The intrinsic unit is constructed by
  `Adjunction.leftAdjointIdIso` from the already published quotient adjunction and
  `normalizedDVRResUnit`. These are canonical adjunction mates, not arbitrary isomorphisms.

The two other proof dependencies `lem-coef-finite-hom-domain-calculus` and
`lem-coef-closed-scalar-domains` have no recorded Lean declarations in the read clone.
Their domain-preservation uses are explicitly retained in the theorem's proof docstring;
there is no declaration to import. They are not needed to type the statement: every arrow
is defined on the ambient derived category and only invertibility is restricted to ctf
inputs. No additional domain-preservation assumption is introduced.

Edge cases checked against the equations: N=1 is the singleton Fin 1 and includes the unit
clause; i=j, j=r and all three equal are admitted by non-strict inequalities; all positive
quotient exponents occur. Zero complexes and zero targets are allowed by P; arbitrary zero
maps t are allowed by target_naturality. The empty scheme is not excluded. The two-step
cocycle is well typed on ambient derived objects and therefore also accepts F_ij K without
silently demanding an extra ctf proof. Characteristic is controlled by D and l ≠ D.p.
No finite projective dimension or flatness of A_j over A_i is assumed.

Searches performed through msearch.py (queries/results retained in searches.jsonl):

- LeanFinder: `derived internal Hom scalar extension compatible target family evaluation
  identity cocycle`, eight hits, including module scalar-extension adjunction formulas and
  `LightCondensed.ihom_map_val_app`; no finite coefficient target-family theorem.
- Loogle: `"ihom", "ev"`, twelve hits in generic monoidal closed category evaluation and
  transposition; none states this scalar tower/target-family result.
- Mathlib grep: `ihom.*(ev|naturality)|expComparison` in CategoryTheory/Monoidal/Closed,
  twenty-one hits. Read Basic.lean evaluation naturality and Functor.lean's Cartesian
  expComparison; neither gives the derived coefficient result.
- LeanSearch: `derived internal Hom coefficient target change evaluation cocycle`, eight
  cochain Hom-complex and presheaf cocycle hits; no match.
- Project rg over lean/WeilConjectures and lean/Sheaf for finite-Hom/coefficient-Hom and
  target/coherence names located the finite-Hom comparison and the canonical scalar-unit
  interfaces used here. Exact node-id search in both source trees found no declaration.
  Exact proposed helper/declaration-name searches in those trees and
  dag/lean_names_upstream.json found no collision. No second definition of the underlying
  sites, coefficient rings, derived categories, tensor, Hom or canonical comparisons is made.

Validation: scompile.py Q90 lem-coef-finite-target-change-coherence compiled this file
in server sandbox mode (4.8 s) and library mode (4.4 s), with no errors or warnings.
Every binder is explicit with `set_option autoImplicit false`. Lines are at most 100 columns.
The only change since that compile is making the existing statement-dependency import of
BasicOperationsCoefficientReduction public; the dry run recompiles the final source.
Dry run: deliver2.py --no-push printed OK, commit aa74981ec19, with the final public-import
source passing preflight and compilation. No statement correction or STATEMENT-DISPUTED
issue was needed.

## Second reading by Q90

Author's second pass, not an independent review: the dispatcher explicitly prohibits
starting a second agent and the maintainer independently reviews this delivery.
I reopened the node and final file and checked each of the above hypotheses and six clauses.
The first pass had an incorrect explicit argument to Ideal.Quotient.factor_eq; I repaired it
using `(S := ...)` and the server then accepted both modes. On the second pass I checked the
variance-sensitive parts separately: the source naturality starts at F H_i(L,Omega_i),
the quotient cocycle has α_H at its left and H(α_K.inv,1) at its right, and the unit similarly
has H(ε_K.inv,1). For target maps the family condition and square use t in the covariant
variable with no invertibility requirement. I also verified Fin N means exactly the stated
positive levels, the family imposes only ctf and the supplied u unit/cocycle, and the main
theorem retains separated finite type instead of imposing properness. The public import
visibility was corrected for the already recorded BasicOperations statement dependency.
Added the existing canonical-unit node to stmt_deps because its declaration is used directly.
No mathematical clause or hypothesis changed in this second pass.
