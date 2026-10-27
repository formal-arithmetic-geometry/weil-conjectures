## Worker report

The module `Sheaf.WeilSheaf.NativeImmersionHeartLocalization` states the complete node in
three declarations, all with `sorry` proofs:

- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeImmersion_coefficientComparisons` gives the
  canonical coefficient isomorphisms as morphisms of ring objects and the two Frobenius
  compatibility squares.
- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeImmersion_exact_constructible` gives abelianity,
  exact forgetting with reflection of exact and short exact sequences, and additivity,
  finite limit/colimit preservation and constructibility preservation for all four functors.
- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeImmersionHeartLocalization` gives adjunctions
  for the specified functors, the four unit/counit carrier identities and their natural
  localization short exact sequence.

There are no new definitions, auxiliary nodes, dependency repairs or statement corrections.
The only node field changed is `lean`. The declarations' docstrings reproduce the relevant
numbered proof steps and dependency citations from the DAG; collectively they contain all ten
steps. Nothing is proved in this stage-2 delivery.

Hypotheses, present explicitly in each of the three signatures:

| Node hypothesis or convention | Lean rendering |
| --- | --- |
| Finite field k₀ | `(k₀ : Type u) [Field k₀] [Finite k₀]` |
| Algebraic closure k and geometric base changes | The framework's fixed `AlgebraicClosure k₀`, used by `(W ↘ Spec (CommRingCat.of k₀)).geometricFiber`. This is exactly the dependency's recorded canonical algebraic closure convention. |
| Prime ℓ different from the characteristic | `(l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]` |
| Ω is the specified algebraic closure of ℚℓ with its native topology | The imported framework uses `PadicAlgCl l`, `WeilCoefficients.{u} l`, and the locally finite continuous coefficient sheaf. No coefficient object is a parameter or a private replacement. |
| X,U,Z are k₀-schemes | `(X U Z : Scheme.{u})` and the three explicit `.Over (Spec (CommRingCat.of k₀))` binders |
| X locally of finite type | `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]` |
| X quasi-compact | `[QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]` |
| X quasi-separated | `[QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]` |
| j:U→X is a quasi-compact open immersion over k₀ | `(j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]` |
| i:Z→X is a closed immersion over k₀ | `(i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]` |
| Complementary images | `(hij : IsCompl (Set.range i.base) (Set.range j.base))` |
| Same coefficient, module and fixed-pair categories | The imported `adicConstantSheaf`, `AdicSheaf`, `ProEtaleWeilSheaf` and `WeilSheaf.objectProperty`; the last is the underlying native constructibility predicate, not a different heart or coefficient stage. |

No hypothesis of separatedness of X, nonemptiness of U or Z, reducedness of Z, positive
rank, or constructibility of M is imposed. The consequences that U and Z are locally of
finite type are not added as assumptions. The single universe `u` follows the framework's
scheme/finite-field universe; its sheaf categories retain the native object universe `u+2`
and morphism universe `u+1`, with `WeilCoefficients.{u}` retaining the prescribed lift.

Clause-by-clause interpretation:

1. For each of j and i, `Scheme.Hom.geometricFiberMap h (comp_over h ...)` is its actual
   geometric base change. `IsIso (upperStarAdicConstantSheafHom l ...)` is invertibility
   of the canonical adjoint of precomposition. `IsMonHom` uses the existing pointwise ring
   object structures and the standard monoidal image structure on the inverse image. The
   underlying morphism is already linear, hence additive; `IsMonHom` supplies preservation
   of multiplication and 1. Together these say isomorphism of ring sheaves.
2. The following equality in each coefficient block compares the two composites from
   h̄* F_X* B_X to B_W. One first applies h̄* of the canonical Frobenius coefficient map and
   then the coefficient map of h̄; the other first applies `upperStarCompIso` of the actual
   equation h̄ F_W = F_X h̄, then F_W* of the coefficient map of h̄ and finally the canonical
   Frobenius coefficient map. This is compatibility with geometric Frobenius, with no chosen
   replacement comparison. The framework realizes F* as the pushforward along F⁻¹; its
   canonical identification with inverse image is `adicUpperStarIsoLowerStarInv`. The
   normalization on coefficients is the existing
   `upperStarIsoLowerStarInv_hom_app_comp_adicConstantSheafLowerStarIso_hom` from
   `WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheafTransport`.
3. For each W=X,U,Z, `Nonempty (Abelian (ProEtaleWeilSheaf k₀ l W))` states abelianity.
   `Abelian` carries data in Lean, so it is expressed as `Nonempty` in this theorem, while
   the pre-existing native instances remain the ones used to type exactness. The two
   `PreservesFiniteLimits/Colimits (IsoAlgebra.forget ...)` clauses express exactness of
   forgetting. For every `S : ShortComplex ...`, the two biconditionals for `S.Exact`
   and `S.ShortExact` express preservation and reflection, including the mono and epi
   endpoint conditions. The functor is precisely forgetting to `AdicSheaf`, not forgetting
   further to the discrete-coefficient sheaf category.
4. The next four blocks use exactly `ProEtaleWeilSheaf.upperStar k₀ l j`,
   `ProEtaleWeilSheaf.upperStar k₀ l i`, `ProEtaleWeilSheaf.extensionByZero k₀ l j`, and
   `ProEtaleWeilSheaf.lowerStar k₀ l i`. Each block states `.Additive`,
   `PreservesFiniteLimits`, `PreservesFiniteColimits`, and preservation of
   `WeilSheaf.objectProperty` for every input satisfying it. Thus P,Q,J,I have all the
   requested properties in the native categories with their framework Frobenius lifts.
5. The final declaration quantifies `aj : extensionByZero ... ⊣ upperStar ...` and
   `ai : upperStar ... ⊣ lowerStar ...`. These are adjunctions of the actual functors,
   not arbitrary functors having isomorphic values. Four universally quantified equations
   specify the carrier maps of the unit and counit of both adjunctions as the maps of
   `adicOpenImmersionLowerShriekAdjunction` and `adicUpperStarLowerStarAdjunction` on the
   geometric fibers. In particular both arrows in the final short complex are normalized.
6. For every M in the entire native fixed-pair category, the last clause supplies
   `h : aj.counit.app M ≫ ai.unit.app M = 0` and asserts
   `(ShortComplex.mk (aj.counit.app M) (ai.unit.app M) h).ShortExact`. Its objects are
   definitionally JP(M), M, IQ(M); its arrows are those same actual counit and unit.
   `ShortExact` gives exactness, a mono first arrow and an epi last arrow. Naturality is
   part of the adjunctions' unit and counit data, and a single pair of adjunctions works
   for every M. Both arrows are morphisms of fixed pairs, hence already satisfy the
   requisite Frobenius equations. No constructibility condition is imposed on M here.

Dependency declarations read and used:

- `def-sf-native-weil-derived-framework`: public entry module
  `WeilConjectures.WeilSheaf.LowerShriek`. Read `WeilComplex.derivedLowerShriek`,
  `WeilComplex`, `WeilComplex.objectProperty`, `ProEtaleWeilSheaf`,
  `WeilSheaf.frobeniusPullback`, `WeilSheaf.objectProperty`,
  `ProEtaleWeilSheaf.upperStar`, `ProEtaleWeilSheaf.lowerStar`, and
  `ProEtaleWeilSheaf.extensionByZero` in their owning `WeilSheaf.Category`,
  `WeilSheaf.LowerStar`, `WeilSheaf.OpenImmersion`, and `WeilSheaf.LowerShriek` modules.
  Read `PadicAlgCl.locallyFiniteFunctions`, `ProEtale.adicConstantSheaf`,
  `ProEtale.AdicSheaf`, `ProEtale.IsAdicLisseSheaf`,
  `ProEtale.IsAdicStratifiedLisseSheaf`, `ProEtale.IsAdicConstructibleSheaf`,
  `adicUpperStar`, `adicLowerStar` and `adicUpperStarLowerStarAdjunction` in the
  corresponding `SixFunctors.ProEtale.Adic.ConstantSheaf`, `Module`, `Constructible`
  and `GeometricFrobenius` sources. These signatures and docstrings specify the native
  coefficient object, the finite ranks per covering member, and the actual Frobenius lifts.
- `def-weil-quasi-separated-morphism`:
  `AlgebraicGeometry.QuasiSeparated` in `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `AlgebraicGeometry.QuasiCompact`
  in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.

The full recorded signatures and docstrings of these statement dependencies were inspected.
The former example `Sheaf.CategoryTheory.CompactObject` is withdrawn; its recorded upstream
replacement `WeilConjectures.CategoryTheory.CompactObject` was read for the header/docstring
conventions. The current Stacks proofs of `lemma-ses-associated-to-open` (09AH) and
`lemma-closed-immersion-complement-retrocompact-exact` (09BM) were read, together with the
ringed sequence in the latest blueprint's `det-sf-open-closed-sequence-ring-sheaf`.

The modules of the stated proof dependencies are imported without `public` where they are
not also required publicly by the statement. This includes the native Constructible and
ExtensionByZero modules, `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`,
`Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`,
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`,
`Sheaf.CategoryTheory.EquivalenceAdjunctionComparison`,
`WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction`,
`Sheaf.AlgebraicGeometry.NativeWeilOpenExactConstructible`, and
`Sheaf.Paper.SfClosedPartitionModuleTest`. The Mathlib leaves for immersion base change and
qcqs permanence are in the public geometry imports; affine Noetherianity uses the
Noetherian-spectrum proof import. The native abelian and framework modules are also
explicitly imported. No stated proof dependency is left waiting.

Edge cases checked before writing:

- U empty: no nonempty assumption; JP(M)=0 and the stated short exact sequence makes the
  closed unit an isomorphism. The native zero sheaf is lisse with rank zero.
- Z empty: no nonempty assumption; IQ(M)=0 and the stated short exact sequence makes the
  open counit an isomorphism.
- X empty: both outer schemes are empty by the image-complement and immersion assumptions;
  the same statement remains meaningful in their zero module categories.
- Nonreduced Z: the closed-immersion class only asks for a closed embedding and surjective
  stalk maps. No radical ideal, reduction, or étaleness of i is used.
- Zero objects and rank zero: the underlying constructibility definition permits `Fin 0`;
  none of the clauses add positive rank or nonzero-sheaf conditions.
- Arbitrary nonconstructible M: the final quantifier is over `ProEtaleWeilSheaf`, not the
  full subcategory `WeilSheaf`. Thus the short exact sequence has the node's full scope.
- Nonseparated X: no separatedness assumption is present. X is only qcqs and locally of
  finite type as required.

Searches for an existing declaration (2026-10-24):

- `msearch.py`, LeanFinder: “For native pro-etale Weil sheaves complementary open closed
  immersions yield an exact sequence extension by zero restriction and closed direct image,
  preserving constructible sheaves”. Eight Mathlib hits, including Mayer–Vietoris exactness
  and unrelated profinite exactness; none states this native Weil localization package.
- `msearch.py`, Loogle: `CategoryTheory.ShortComplex.ShortExact,
  CategoryTheory.Endofunctor.IsoAlgebra.forget`. The remote Mathlib index does not know
  the project-only IsoAlgebra declaration. A corrected query
  `CategoryTheory.ShortComplex.ShortExact` returned 12 hits, including its exact/mono/epi
  definition. It is used directly; it is not the desired geometric theorem.
- `msearch.py`, grep: `shortExact.*[oO]pen|[oO]pen.*[cC]losed|map_shortExact` in
  `CategoryTheory`. Fourteen broad name/doc hits; no native Weil theorem.
- `rg` on the project's `WeilConjectures` tree for the item id: no hit. Searches for
  `shortExact`, `openClosed`, adjunction/unit/counit and `IsCompl` in the WeilSheaf
  immersion, adjunction, localization and triangle sources found individual native
  exactness and adjunction facts, but no declaration giving this entire node.
- `rg` on `lean/Sheaf` for native immersion, heart localization and open–closed short exact
  sequences found the native open-exact-constructible and ringed localization inputs,
  not this theorem. Searches of both project trees and `dag/lean_names_upstream.json`
  for all new declaration names found no collision.

No STATEMENT-DISPUTED flag or source discrepancy was found. An initial elaboration required
opening the existing `CategoryTheory.Obj` scope to make the canonical image monoid structure
available to `IsMonHom`; this introduces no definition or instance of our own. Server
`scompile.py` then compiled the sandbox and intended library module cleanly (3.5 and 3.6 s).
The final import list is checked again by the required compiler and delivery preflight.

## Second reading by Q51

This is an author verification pass; the dispatcher forbids starting another agent and the
maintainer performs the independent review. I reopened the node and the delivered source
and matched every hypothesis and clause as tabulated above. The checks specifically covered
the native B-module carrier category, actual geometric-fiber maps, both Frobenius coefficient
squares, all three forgetful functors, each of the four functors' additive/finite-exact/
constructible clauses, all four adjunction carrier identities, and the final quantifier over
all M. The arrows of the ShortComplex refer to `aj` and `ai` from the same preceding
existential binders. Hence the normalization statements and sequence cannot concern different
adjunction choices. There is no extra separation, reducedness, nonemptiness, finite-rank
uniformity, or constructibility hypothesis. The source's nilpotent and empty cases survive
unchanged. The signature recorded in `lean.statement` is copied verbatim from the main
localization declaration, and `lean.declarations` records its two companion clauses.
