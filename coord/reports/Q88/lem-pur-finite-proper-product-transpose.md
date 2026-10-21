## Worker report

The module `Sheaf.Paper.FiniteProperProductTranspose` states
`WeilConjectures.FiniteProperProduct.finiteProperProductTranspose` with one `sorry`,
and defines the displayed maps by real composites of the recorded operations.
The original statement, dependency lists, proof and other node fields are unchanged.
No new mathematical notion, new node, dependency repair, or statement correction is needed.

Hypotheses and objects, matched individually:

- `P : PurityFiniteSetting.{u}` supplies the fixed finite-field datum, ell distinct
  from p, finite coefficient extension, uniformizer quotient and positive level.
  `A P` abbreviates the recorded `finiteCoefficientRing` at exponent
  `(P.level - 1) + 1`. Since `P.level_pos : 1 ≤ P.level`, that exponent equals
  `P.level`, so every allowed level, including 1, is retained. The subtraction
  is solely the indexing convention of `finiteDerivedPullback` and
  `finiteIntrinsicDerivedTensor`, whose index n means exponent n+1.
- Each of `B Y Z : Over (Spec (.of P.field.k))` is a k-scheme with its actual
  structure morphism. Each has its own `IsSeparated`, `LocallyOfFiniteType`,
  and `QuasiCompact` structure-morphism binders. The last two together mean
  finite type, as in the recorded scheme-morphism definitions.
- `a : Y ⟶ B` and `b : Z ⟶ B` are morphisms over k; the `Over` morphisms
  include the two commutation conditions. `IsProper a.left` and
  `IsProper b.left` give exactly the required properness assumptions.
- The actual chosen fibre product is `pullback a.left b.left`, with
  `pullback.fst` and `pullback.snd`. The composite c is written t followed
  by b; `pullback.condition` identifies it with r followed by a.
- `H : D P Y.left` and `J : D P Z.left` are arbitrary ordinary unbounded
  derived objects. `D` is the existing `proEtaleDerivedCategory`, over
  the constant coefficient ring sheaf on the small pro-etale site. The
  site retains object universe u+1 and morphism universe u.
- F and G are literally `(push P a.left).obj H` and `(push P b.left).obj J`.
  `external` abbreviates exactly the tensor of the two pulled-back objects E.
  No alternative category, boundedness, etale origin, constructibility,
  finite Tor amplitude, support comparison, exceptional adjoint, or
  invertibility condition is introduced.

Map definitions, matched to the node:

- `pull`, `tensor`, `sigma` are aliases/specializations of the published
  finite pullback, intrinsic tensor, and signed K-flat braiding.
  `residueInverse` obtains the source-implied inverse of ell by mapping
  the existing local-ring unit theorem to the residue field. It adds no
  hypothesis or postponed theorem. `mu` is the exact existing
  `canonicalFinitePullbackTensor`, with those inherited inverses.
- `adj` is the published section-normalized inverse-image adjunction,
  derived by `mapDerivedCategoryRightDerivedAdjunction`. `comp` is the
  existing intrinsic termwise canonical pullback compositor, the finite
  realization of the general canonical pullback-composition dependency.
- `theta` is comp(t,b) inverse, the square equality, then comp(r,a).
  `exchange` is `mateEquiv` of this exact comparison, using the two
  ordinary derived adjunctions. Its orientation is Pb Ra to Rt Pr.
- `projection` is the component formula of def-exchange-projection:
  the ordinary Hom bijection applied to mu followed by epsilon tensor
  identity. This is a finite intrinsic specialization of the supplied
  counit-projection definition, not an arbitrarily supplied map.
- `v` is tensor(exchange,identity) followed by projection(t).
  `w` is sigma(F,G), projection(b;J,F), then Rb(sigma(J,PbF)).
  `omega` is w, then Rb(v), then kappa inverse, in that order.
- `realization` is the published canonical derived equivalence with
  fixed-scalar sheaves. `pushModel` uses its section/K-injective-normalized
  direct-image comparison. `iteratedPushModel` inserts only that equivalence's
  unit at the middle scheme. `kappa` transports exactly the recorded
  `ProEtale.finiteDirectImageComposition` through these isomorphisms;
  it is not defined by choosing some adjunction or some isomorphism.
- `swapTensor` pulls the reversed tensor through the actual
  `pullbackSymmetry`; its component identifications use the existing
  comp and the two projection equations for that same swap, then sigma.
  `swapPush` is Rc'(eta_s), kappa inverse, the equality c's=c, then
  Rc(swapTensor), precisely the transport S in the node's proof Step 6.

Conclusions, matched clause by clause (the theorem is a conjunction):

1. The inverse Hom bijection for t on v equals mu_t followed by
   tensor(theta_F followed by Pr(epsilon_a), identity). This is the
   stated v-hat after the specified source comparisons.
2. The inverse Hom bijection for b on w equals mu_b followed by
   tensor(identity,epsilon_b), the stated w-hat.
3. The inverse Hom bijection for c on omega equals mu_c followed by
   tensor(Pr(epsilon_a),Pt(epsilon_b)), with both canonical composition
   comparisons and c=ar=bt written explicitly on the source.
4. The same transpose equals comp(t,b) followed by the inverse Hom
   bijection of `(adj P b.left).comp (adj P t)` on w followed by Rb(v).
   This retains the actual composite-adjunction identification with kappa.
5. That composite inverse Hom bijection equals Pt(w-hat) followed by
   v-hat. Clauses 4 and 5 together give exactly the node's in-particular
   assertion; neither clause assumes arbitrary compositor compatibility.
6. `omega a b H J = sigma(F,G) ≫ omega b a J H ≫ swapPush a b H J`,
   the claimed forward-map symmetry with the specified S and signed sigma.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  its finite extension and coefficient-ring conventions, and
  `PurityFiniteSetting.coefficientPrime_isUnit_stalk`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.condition`,
  `pullbackSymmetry`, and its two projection equations.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteCoefficientRing`,
  `finiteDerivedPullback`, `finiteIntrinsicDerivedTensor`,
  `finiteIntrinsicClosed`, `finiteIntrinsicTensorModels`.
- `Sheaf.Paper.DerivedPullbackTensorIso` and its public finite-comparison
  module: `derivedPullbackTensorIso`, `canonicalFinitePullbackTensor`,
  `pullbackTensorBraiding`, `pullbackTensorCoefficientFinite`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the recorded supplied
  exchange/projection interface and its defining formulas; the present
  finite component specializations use `mateEquiv` and `Adjunction.homEquiv`
  directly, with the prescribed actual functors and comparisons.
- `Sheaf.Paper.FiniteDirectImageComposition`:
  `AlgebraicGeometry.ProEtale.finiteDirectImageComposition`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`: the reexported full
  `integralTowerGeneralPullbackComposition` / canonical ring-sheaf
  comparison. The intrinsic presentation's termwise specialization is the
  already published `sfIntrinsicDerivedPullbackComp`; it is also the
  composition used by the recorded finite tensor comparison's composition law.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`,
  `Adjunction.homEquiv`, and the explicit composite Hom bijection.
- The normalization helpers use the existing
  `sfIntrinsicDerivedEquivalence`, `sfIntrinsicDerivedDirectImageComparison`,
  and `sfIntrinsicConstantModuleAdjunction`, publicly available through the
  finite tensor-comparison dependencies.
- The stated proof dependencies `RingedDerivedMonoidalComparisons`,
  `ProEtaleConstantRingComposition`, and `IsoSectionwiseInverseImage` are
  imported for stage 3. Other recorded proof dependencies are already public
  statement imports. No import of a downstream product-symmetry theorem occurs.

Edge cases checked mathematically before stating:

- Level 1 is index 0, giving exactly O_E/(varpi); arbitrary positive levels,
  including nonreduced quotients at n>1, require no coefficient flatness.
- Zero H or J and empty Y or Z preserve the types and all displayed maps.
  Empty schemes do not require a chosen point or a nonempty site object.
- Identity a or b and Y=Z=B reduce to the ordinary tensor-counit calculation;
  the identity-normalized compositor and source comparisons are retained.
- Odd cohomological shifts retain both signed braidings in w and the actual
  signed braiding in swapTensor, so the Koszul signs are never discarded.
- Unbounded H,J and tensors which leave the bounded constructible category
  are still in the exact ambient categories quantified by the theorem.
- No assumption that exchange, projection, or omega is invertible occurs.

Searches performed on 2026-10-21:

- `msearch.py ... leanfinder "The external product defined by derived exchange
  and projection has transpose the tensor of counits and is symmetric"`:
  eight generic external-product/Frobenius hits, including
  `MonoidalCategory.externalProductSwap`, `prodCompExternalProduct`,
  `externalProductCompDiagIso`, and `CategoryTheory.frobeniusMorphism`.
  None states the three specified transposes, compositor normalization,
  and finite pro-etale forward-map swap identity.
- `msearch.py ... loogle "CategoryTheory.Adjunction.comp_homEquiv,
  CategoryTheory.Adjunction.rightAdjointProjectionMap"`: no hits; Loogle
  reports the second identifier unknown because it is upstream, not Mathlib.
  The actual upstream ProjectionMap file and Mathlib Adjunction.Basic were
  read directly, including the right-adjoint projection component and comp.
- `msearch.py ... grep "externalProduct|rightAdjointProjectionMap|comp_homEquiv"
  CategoryTheory`: 25 hits, principally `Adjunction.comp_homEquiv` and
  generic monoidal external products. These supply pieces, not the item.
- `rg` in project `lean/Sheaf` and source `lean/WeilConjectures` for the item id,
  `finiteProperProduct`, `properProductTranspose`, `externalProduct`, and
  tensor/counit patterns found no existing item declaration. Read the upstream
  `FiniteCoefficient/Derived/ExternalProduct.lean`: it only defines the
  external object in fixed-scalar coordinates, not these map identities.
  `CompositeTensorTranspose` concerns a different composite projection problem.
- `grep -rn "lem-pur-finite-proper-product-transpose" lean/WeilConjectures`
  returned no declaration. The existing ingredient definitions were reused.

No STATEMENT-DISPUTED issue or node fault was found. The source equation preceding
Stacks 0E48 defines the ordinary projection map on all unbounded objects; the
blueprint symmetry paragraph identifies the two pulled-back counits. The node's
seven-step proof supplies the additional explicit calculation, as its provenance says.

## Second reading by Q88

A second in-session reading compared the completed file with the original node;
the maintainer's independent delivery review remains separate. Checked all three
scheme properties on each of B,Y,Z, both properness hypotheses, the Over morphism
conditions, arbitrary ambient H,J, and the six conclusion clauses listed above.
The selected c=t followed by b agrees with r followed by a via the existing
pullback condition. Checked theta's direction, the order of both symmetries in w,
kappa's direction Rc to RbRt, and the target of the actual swap transport.
Checked that the fourth and fifth clauses use the composite adjunction, rather
than asserting compatibility for arbitrary isomorphisms. The level-1 indexing
is legitimate by P.level_pos; no characteristic or positivity case is dropped.
The first compilation caught an incorrect invocation of the implicit arguments
of pullback.condition and a residue-unit elaboration error; both were corrected
without changing any mathematical statement. Every helper contains real data;
only the item theorem is postponed. No additional agent was started, as instructed.
