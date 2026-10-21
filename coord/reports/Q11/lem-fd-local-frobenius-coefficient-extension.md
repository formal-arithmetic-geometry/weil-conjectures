## Worker report

The module `Sheaf.Paper.LocalFrobeniusCoefficientExtension` states
`WeilConjectures.localFrobeniusCoefficientExtension`, with its proof `sorry`.
`LocalFrobeniusCoefficient.Properties` spells out all four displayed equalities
and the identity-extension assertion. The remaining declarations construct the
maps in those equalities from the published functors and comparisons; they do
not introduce an independent coefficient category, an arbitrary comparison,
or an integral lattice. No new nodes or dependency-module repairs are needed.
The source is the current blueprint's
`sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`, displayed local
alternating trace, with the extracted comparison argument in this DAG node.

Hypotheses and conventions:

- The finite-field tuple is `D : FiniteFieldDatum.{u}`. The prime distinct from
  `D.p` and the chosen algebraic closure of the padic field are supplied by
  `c : D.CoefficientDatum` (`c.l`, `c.different`, `c.Qbar`).
- Finite subextensions are `F L : Padic.FiniteCoefficientFields c.l c.Qbar`;
  `hFL : F ≤ L` gives exactly `IntermediateField.inclusion hFL`. No topological
  continuity assumption is imposed on an unspecified embedding.
- The model scheme is `X₀ : Over (Spec (.of D.k₀))`. Finite type is
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`; separatedness is
  `[IsSeparated X₀.hom]`. Properness is not assumed.
- The geometric fibre is the recorded `(D.geometricFiber X₀).left`; its Galois
  Frobenius is `(D.geometricFrobenius X₀).hom`. The point scheme is
  `Spec (.of D.k)` with Frobenius `(frobeniusPointIso D).hom`.
- The directive to use the specified comparison family is represented by
  `C : IntegralComparisonSystem c.l` and its
  `IntegralComparisonRealizationCoherence` witness `_hC` at `F.val`, `L.val`,
  and the actual inclusion. These are the realization-normalized comparison
  choices stipulated in the question, rather than an extra assumption on X,
  an object, a lattice, or finite reductions. The dependency theorem supplies
  such systems. The conclusion is valid for any system with that normalization.
- The node's positive `n` is `r+1`, and its point is
  `x : D.extensionPoints X₀ (r+1) (Nat.succ_pos r)`. The lift is the recorded
  `localExtensionPoint`; the recorded `localExtensionPoint_return` supplies the
  semilinear equality used in the return map. The independent positive Weil
  iterate in the second assertion is `j+1`.
- Every constructible object has type `sfRationalConstructibleCategory ...`;
  every Weil pair has type `sfWeilComplex ...`. Thus the categories are the raw
  rationalizations, and the morphisms range over their full Hom groups.
- `scalar` instantiates `sfRationalScalarExtension`, with auxiliary prime-
  characteristic parameter zero as in `pointRationalFibreScalarIso` and the
  normalized comparison API. This parameter supplies no restriction on schemes.
  Ordinary point-complex scalar extension is `DerivedCategory.pointFdScalarExtension`.

Constructions and conclusions, in diagrammatic Lean composition order:

- `pullback ... E j` is G_(E,j+1), using `rationalDerivedPullback` at the actual
  positive power. `fibre ... E xbar` is P_E followed by Q_E, using the recorded
  `pointRationalFibre`.
- `comparison ... C j` is a_(j+1), the published
  `LocalFrobeniusTransport.rationalScalar`, whose component formula is the
  rationalization of `integralComparisonScalar = lambda followed by mu inverse`.
- `pointComparison ... C xbar M` constructs the specified **isomorphism** b_M:
  the inverse component of `pointRationalFibreScalarIso`, followed by
  `pointRationalFibre.mapIso` of that same specified point-pullback scalar
  comparison. Its hom has the formula of the already published
  `LocalFrobeniusTransport.rationalFibreScalar`.
- `extend` is `IsoAlgebra.mk (T.obj K.carrier) (a_1.symm ≪≫ T.mapIso K.str)`;
  hence its structure is exactly T(theta) composed with a_1 inverse.
- `iterate` follows the recorded `localWeilIterate` recurrence, instantiating its
  compositor with `LocalFrobeniusTransport.rationalComposition ... C` as explicitly
  required by this item's normalization directive. This is the published
  strict-system realization, not an arbitrary isomorphism chosen by existence.
  Its base case is the actual rational `K.str`. The only difference in presentation
  from `localWeilIterate` is that the specified family C is explicit, instead of
  leaving the existential compositor choice in `integralPullbackComposition`
  implicit. Point iteration is reused directly from the normalized dependency.
- `returnTransport` is the published `LocalFrobeniusTransport.rationalTransport`:
  successive rational point transports followed by Q of the comparison arising
  from the actual semilinear scheme-map equality. This is R_H on every object,
  including objects without a Weil structure.
- `operator` is `returnTransport ... K.carrier ≫ fibre.map (iterate ... K).hom`,
  exactly the local-operator recipe of `localFrobeniusOperator`, instantiated
  with the stipulated compositors, so it is D_H(eta^[n]) R_H.
- The first conjunct of `Properties` quantifies over **all** M, N and rational
  v : M ⟶ N and states `T_pt.map (D_F.map v) ≫ b_N.hom =
  b_M.hom ≫ D_L.map (T_X.map v)`. Every b is an actual isomorphism by its definition.
- The second conjunct quantifies over every rational Weil pair K and j : Nat;
  `a_(j+1).hom ≫ theta_L^[j+1].hom = T_X.map theta^[j+1].hom` is exactly the
  iterated-structure equality for every positive iterate.
- The third conjunct quantifies over every constructible M and states
  `T_pt.map R_F(M) ≫ b_(G_F M).hom ≫ D_L.map a_n.hom =
  b_M.hom ≫ R_L(T_X M)`, exactly the return-transport equation.
- The fourth conjunct quantifies over every rational Weil pair K and states
  `T_pt.map F_F(K) ≫ b_K.hom = b_K.hom ≫ F_L(extend K)`, the intertwining equation.
- The last conjunct uses the identity inclusion `AlgHom.id` and states, after
  the faithful inclusion of finite-dimensional point complexes into their derived
  category, `b_M.hom ≫ D_F.map (sfRationalScalarUnit.hom.app M) =
  fieldScalarUnit.hom.app (D_F.obj M)`. Thus b is exactly the identity under the
  specified source and target unit identifications. It does not demand literal
  equality of the tensor object and its unit-identified object. Equality of fields
  gives the same canonical inclusion; no F=L case is discarded.

Recorded dependencies used (module / declarations):

- `Sheaf.Paper.FiniteFieldFiber` / `FiniteFieldDatum`, `CoefficientDatum`,
  `geometricFiber`, `extensionPoints` (through `LocalFrobeniusTrace`).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` /
  `AlgebraicGeometry.IsSeparated`; the finite-type and quasi-compact classes are
  the recorded Mathlib declarations, exposed by the same dependency chain.
- `Sheaf.Paper.LocalFrobeniusTrace` / `localPositivePower`,
  `localExtensionPoint`, `localExtensionPoint_return`; the local iteration and
  operator recipes are instantiated at the explicitly stipulated normalized family.
- `Sheaf.Paper.SfRationalizationKaroubi` /
  `sfRationalConstructibleCategory`, `sfRationalScalarExtension` (publicly exposed
  by `IntegralPullbackComparisonRealization` and `LocalFrobeniusTrace`).
- `Sheaf.Paper.SfWeilSheafComplex` / `sfWeilComplex`,
  `sfWeilPrimeInvertible`, `sfWeilFrobeniusPullback` (via `LocalFrobeniusTrace`).
- `Sheaf.Paper.IntegralPullbackComparisonRealization` /
  `IntegralComparisonSystem`, `IntegralComparisonRealizationCoherence` and
  the representative-normalized integral scalar/composition family.
- `Sheaf.Paper.FiniteCoefficientPoint` / `pointRationalFibre`,
  `pointRationalFibreScalarIso`.
- `Sheaf.SixFunctors.FrobeniusPointTransportNatural` /
  `frobeniusPointTransport_natural`, for proof step 3's point-transport pasting.
- `Sheaf.Paper.IntegralOperationsScalarComparisons` / the scalar pullback
  comparisons, instantiated in the specified realization normalization.
- `Sheaf.Paper.PointSectionsScalarExtension` /
  `pointRationalSectionsScalarExtensionIso`, through its normalized small-fibre
  transport `pointRationalFibreScalarIso`.
- Proof dependency `Sheaf.Paper.LocalFrobeniusTransportNormalization` /
  `rationalComposition`, `rationalScalar`, `rationalTransport`,
  `rationalFibreScalar`, `localFrobeniusTransportNormalization`. This is public
  because it also supplies the prescribed map constructions in the statement.
- The unit clause additionally reuses the existing published unit declarations
  `sfRationalScalarUnit` in `Sheaf.Paper.SfScalarExtensionComposition` and
  `DerivedCategory.fieldScalarUnit` in `Sheaf.Paper.FieldDerivedScalarTower`.

Edge cases checked before drafting: n=1 and iterate=1 are the successor-index
zero cases, with theta^[1]=theta and one point transport. F=L is included via
identity coefficients and is explicitly normalized by the final conjunct. The
zero complex and its unique endomorphism are allowed. An empty X₀ has no extension
point, so the point-indexed assertion is vacuous as in the node. Arbitrary shifts,
non-heart constructible objects, and rational Weil isomorphisms with no stable
integral lattice remain in the domain. No finite-Tor predicate occurs. Prime
invertibility on the geometric fibre and on Spec k is constructed from l≠p,
not added as a hypothesis. Universe u is arbitrary, with the published scheme,
coefficient, and point-category universe conventions retained.

Searches for an existing statement (all through the prescribed search wrapper,
except the direct project-source searches):

- LeanFinder: `Coefficient extension intertwines local Frobenius of constructible
  Weil complexes through point fibre comparisons` returned 8 results on PreTilt
  coefficient Frobenius/perfection; no constructible Weil-complex comparison.
- Loogle: `CategoryTheory.Functor.map_comp` returned 6 generic functor/presheaf
  composition results, including `CategoryTheory.Functor.map_comp`.
- LeanSearch: `Natural scalar comparison for local Frobenius on rational
  constructible Weil complexes` returned 8 unrelated results (matrix Frobenius
  norm, Witt-vector Frobenius and scalar-tower instances).
- Mathlib grep: `localFrobenius|pointRationalFibreScalar|pullbackScalarComparison`
  returned zero results.
- Project rg: `localFrobenius|local.*[Ss]calar|[Ss]calar.*[Ff]robenius` in
  `lean/WeilConjectures` and `lean/Sheaf/Paper` found the recorded local-operator,
  point-comparison and normalized-transport interfaces, but no theorem containing
  the four requested identities. The upstream
  `AlgebraicGeometry.fieldExtendScalarsFrobeniusIso` was read: it is about ordinary
  pro-etale field sheaves and does not state this raw rationalized-complex result.
- Project grep for this item's blueprint id in `lean/WeilConjectures` returned
  zero hits. Direct rg for `localFrobeniusCoefficientExtension` and
  `LocalFrobeniusCoefficient` in both project trees and the upstream-name record
  returned zero hits before the sandbox draft.

Validation: the delivered module compiled with the prescribed scompile.py wrapper,
including its module-path verification, without errors or non-sorry warnings.
All binders and universe variables are explicit; `autoImplicit` is disabled.
There is one postponed theorem, matching this DAG node; all definitions have real data.
No statement correction, disputed mathematical assertion, or dependency fault was found.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
