## Worker report

The delivery states `AlgebraicGeometry.Etale.p1KummerDerivedScalar` in
`Sheaf.Paper.P1KummerDerivedScalar`. Its only theorem has proof `sorry`.
`Sheaf.Paper.P1KummerScalarEndpoints` supplies real definitions of the endpoint
normalizations and actual composites; it contains no `sorry` or postponed theorem.
The original item's mathematical statement is unchanged. Its `stmt_deps` gains only
`def-sp-p1-kummer-scalar-endpoints`.

Source read: the entire Charts paragraph of
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`,
the item's four proof steps, all five statement-dependency records, their recorded
source declarations and docstrings, and the extra K-flat proof dependency. The Charts
paragraph says the Kummer classes are images from the common residue coefficient ring.
The source's fixed O(1), not a chosen cohomology generator, is used throughout.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Noetherian scheme S | `(S : Scheme.{u}) [IsNoetherian S]`; Mathlib's Noetherian scheme includes the finite affine cover condition. |
| N >= 1, invertible on S | `(N : ℕ) (hN : 0 < N) (hS : IsUnit (N : Γ(S, ⊤)))`; invertibility of a global natural-number section is equivalent to invertibility at every stalk. |
| Finite commutative coefficient rings, arbitrary unital map, NA=NB=0 | `A B : Type (u + 1)`, both `CommRing` and `Finite` instances, `φ : A →+* B`, `hA`, `hB`. No flatness, injectivity, surjectivity, nonzero-ring or finite-Tor assumption. |
| Lambda = Z/N, P = P1_S | `p1KummerResidue N = ULift.{u+1} (ZMod N)` and `ProjectiveLine S`. ULift only changes the coefficient universe, not the ring. The annihilation proof is the real `congrArg ULift.up (ZMod.natCast_self N)`. |
| Ordinary etale unbounded module categories | `DerivedCategoryModule`, `ordinaryFiniteUnit`, `ordinaryFiniteLine`, and `scalarExtension`; these use `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} R)`, not the pro-etale site or a bounded subcategory. |
| mu_N and its power action; R_P(1) | `Scheme.finiteEtaleTateLine`, as used by `ordinaryFiniteLine`. It sheafifies the existing roots-of-unity module presheaf with its unique ZMod action, extended to R. Its tensor convention R tensor mu is symmetry-equivalent to the node's mu tensor R. |
| Fixed c_Lambda, Kummer boundary of O(1) with stated transition | `c` with `hc : ordinaryFiniteP1ChernSpec ... c`. That predicate realizes c by exact forgetting and the integral generator and equates it to `ordinaryFiniteP1KummerClass`, whose actual Picard input is `ProjectiveSpace.twist ... 1`, with transition g0=(x1/x0)^(-1)g1. `ordinaryFiniteP1_isUnit` supplies precisely the pullback of hS on P. |
| Canonical unit and Tate identifications for Lambda->A, Lambda->B, A->B | `eA`, `eB`, `e : P1KummerScalarEndpoints ...`. `unit_normalization` sends a to φ(a) on constant-presheaf generators; `line_normalization` sends a tensor z to φ(a) tensor z. `unit_derived` and `line_derived` fix the actual derived arrows by the extension/restriction adjunction, with the exact restriction/single comparison. These equations characterize the balanced maps, not just their cohomology. |
| Canonical residue maps | `p1KummerResidueMap N A hA` is `finiteEtaleTwistScalar` composed with ULift's ring equivalence. The B residue map is written as `φ.comp (p1KummerResidueMap N A hA)` so composition needs no transport proof. This equals the canonical map to B because every unital ring map from Z/N is uniquely determined by one. It is not an extra choice. |
| c_A and c_B are images of that same fixed c_Lambda | `eA.chernImage c` and `eB.chernImage c`: unit inverse, functor image of c, shifted Tate identification. |
| Their adjuncts are the specified h_R | The first two conjuncts give `ordinaryFiniteP1ChernSpec A ... (eA.chernImage c)` and its B counterpart. Thus these are the module-derived Kummer Chern arrows of the dependency, and `ordinaryFiniteP1ChernPushforward` applies the specified inverse-image/direct-image adjunction to them. No additional choice of Chern class is introduced. |
| Canonical alpha: E E_LambdaA -> E_LambdaB | Existing `ProEtale.pbcFixedScalarExtensionComp`, specialized to the small-etale topology. Despite the namespace, this definition is site-generic; its restriction functors here are on the ordinary small-etale site. Its definition is `Adjunction.leftAdjointCompIso` of the actual three scalar adjunctions and `Sheaf.derivedRestrictScalarsCompIso`. This is the adjunction-compatible canonical comparison, not a bare chosen functor isomorphism. |
| Components of alpha are multiplication and shifted balancing | The next two conjuncts explicitly give `E(eA.unitIso.hom) ≫ e.unitIso.hom = alpha.app Lambda ≫ eB.unitIso.hom` and the corresponding equation at `Lambda_P(1)[2]`. Cancelling the transported endpoint isomorphisms gives exactly the component descriptions in the node. |
| Canonical shift understood | `shiftedLineIso` is `Adjunction.LeftAdjointCommShift.iso` for exact scalar restriction, then the shift functor applied to `lineIso`. No locally selected shift structure or notation is hidden in the statement. |
| theta1[2] composed with E(c_A) equals c_B composed with theta0 | Last conjunct: `(scalarExtension φ P).map (eA.chernImage c) ≫ e.shiftedLineIso.hom = e.unitIso.hom ≫ eB.chernImage c`. Lean's `≫` orders composition left to right. This is an equality of morphisms in the entire derived category. |

Dependency interfaces read and used:

- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the full derived category.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `Scheme.finite_etale_torsion_twist_line`; its public finite-twist definitions,
  `finiteEtaleMuModulePresheaf`, `finiteEtaleTwistScalar`, `finiteEtaleTateLine`,
  and `finiteEtaleTateOneGenerator` from the existing signed finite-sheaf interface.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`:
  `exists_ordinaryFiniteP1Adjunction`; its public data expose
  `ordinaryFiniteP1ChernSpec`, `ordinaryFiniteP1KummerClass`, `ordinaryFiniteUnit`,
  `ordinaryFiniteLine`, and `ordinaryFiniteP1ChernPushforward`. The small additional
  public import `OrdinaryFiniteP1KummerMaps` exposes its existing
  `ordinaryFiniteP1_isUnit`; this is a helper in the dependency's interface, not a
  second definition of invertibility.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem,
  including the actual ordinary functor, universal counit, and K-flat computation.
  The already-published ordinary constant-ring specialization is used from
  `Sheaf.Paper.EtaleDerivedScalarTensor`: `scalarExtension`. It is an abbreviation
  for the existing adjoint `pbcFixedScalarExtension`, not a new scalar functor.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons` and
  its public `Composition` record, whose `ordinary_insertion`, `pullback_model`,
  `homEquiv`, and `unit` fields fix the composition on representatives and adjunctions.
  The already-published specialization used in the signature is
  `ProEtale.pbcFixedScalarExtensionComp` in `Sheaf.Paper.WitnessCompatibility`
  (publicly available through EtaleDerivedScalarTensor).
- Proof-only `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and the publicly reexported
  `CategoryTheory.MorphismProperty.kFlat` for ModuleCat-valued sheaves.

All five original statement-dependency modules are public imports. The extra K-flat
proof-dependency module is a plain import. No recorded dependency is replaced.
The generic ringed-topos comparison and cochain change-of-rings nodes have different
category presentations; the already-published constant-ring scalar specialization is
used to express their canonical constructions in the ordinary module-sheaf encoding.

Edge cases checked mathematically before writing and on final reading:

- N=1 forces both coefficient rings to be zero rings. Their units and Tate lines
  are zero objects; all displayed maps and equations remain defined. No Nontrivial
  instance or positive-characteristic-prime assumption excludes this case.
- The empty scheme is allowed, including its zero section ring and empty site.
  Invertibility and all section normalizations are meaningful there.
- The identity coefficient map gives the usual scalar unit and unchanged fixed
  Chern arrow. No arbitrary choice of orientation or local root generator occurs.
- The nonflat quotient Z/4 -> Z/2 with N=4 over Spec Q is covered. Flatness is
  required only of the unit and root lines over their own coefficient rings.
- Composite coefficients use the actual composite ring map, with all three
  extensions on the same ordinary small-etale site. The degree-two shift is even;
  evaluating its representative introduces no tensor sign.
- Arbitrary Noetherian schemes, not just finite-type schemes over a field, and all
  coefficient universes accepted by the dependencies remain available.

Actual duplicate searches (logged by msearch.py in this sandbox):

- LeanFinder: “Derived scalar extension preserves the specified Kummer first Chern
  morphism via the canonical coefficient composition comparison”: eight hits about
  cotangent complexes and Kaehler differentials; none is this statement.
- Loogle: `SheafOfModules.pullbackComp`: five ordinary pullback/coherence hits.
  Read Mathlib `PullbackContinuous.lean:167` and `ModuleCat/ChangeOfRings.lean:984`;
  neither is a derived Kummer statement. Their canonical adjoint construction agrees
  with the existing scalar compositor being used.
- Mathlib grep: `kummer.*scalar|scalar.*kummer|extendScalars.*[Cc]omp`: ordinary
  module scalar composition results, no derived etale Kummer theorem.
- LeanSearch: “Canonical unit and Tate line identifications under derived change of
  coefficient rings with normalization on pure tensors”: eight algebraic tensor
  results, no normalized etale derived endpoint record.
- LeanFinder: “Unit and Tate line endpoints for derived scalar extension normalized
  on pure tensors”: eight cotangent/formal-unramified results, no such record.
- Mathlib grep: `P1KummerScalarEndpoints|derived.*Tate.*[Cc]oefficient|[Cc]oefficient.*Tate.*[Ee]ndpoint`:
  no hits.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the new names: no existing declarations. Upstream search for the item ID:
  no hit. Concept searches found the existing scalar functor and compositor, which
  were reused, and the ordinary finite P1 Kummer interpretation, which was reused.
- DAG and blueprint search for scalar endpoints: no blueprint match. The existing
  signed-line scalar normalization node is about arbitrary ring-sheaf tensor powers
  and dual comparisons, not these ordinary derived unit/root endpoint data.
  The downstream P1SplittingScalar helper definitions are not imported (they would
  close the dependency cycle); its scalar single map takes an ordinary extension
  arrow, whereas the new small helper derives a restriction-valued insertion.

No STATEMENT-DISPUTED flag or mathematical statement correction. No dependency
modules or repairs. No proofs have been attempted.

## New nodes

`def-sp-p1-kummer-scalar-endpoints` defines the normalized endpoint record and the
actual derived insertion, shifted comparison and Chern-image composites, with trivial
residue-ring notation and its canonical coefficient map. Its source is the Charts
sentence and the explicit endpoint identifications of the dispatched item. Its statement
introduces all objects and cites the existing ordinary finite P1 Kummer-class definition
and derived change-of-rings node. Its imports use those exact notions. The record only
specifies normalization; it does not assert existence. Existence is supplied by the
item's theorem. The searches above were run and their exact logged results are in the
new node's `mathlib_searches`; no existing DAG/Mathlib/project declaration packages
these endpoints. The blueprint ancestor is det-sp-reduction-exceptional, via the item
and lem-sp-p1-splitting-scalar. This addition leaves the original statement untouched.

## Second reading by Q93

Final clause-by-clause self-check of both modules against both JSON statements; the
maintainer's independent delivery review remains separate. The initial elaboration
found that `ordinaryFiniteP1_isUnit` was a non-public proof import of the adjunction
module, so its owning module is imported publicly. A proposition-valued abbreviation
was removed: the residue-annihilation proof now appears literally as `congrArg`.
The final theorem additionally spells out that both scalar images satisfy the
existing Chern predicate, so the phrase identifying their adjuncts with the specified
h_R is retained. Constants and Tate generators pin the endpoint data; the derived
adjunction pins their actual derived maps, and the canonical compositor is the existing
one, not an existentially unconstrained alpha. The last equation has source E(A_P)
and target B_P(1)[2]. Every universe and binder is explicit (`autoImplicit false`);
there are no local instances, private declarations, local notation, let-bindings in
statements, hollow objects, or extra flatness hypotheses. All source lines fit 100
characters. The new definition node contains no postponed proof.

## Validation

Both final modules passed scompile.py separately in dependency order, including the
Chern-realization conjuncts (9.3 s and 10.3 s for their library checks), with no errors
or unexpected warnings. The first delivery dry run rejected the new definition node
for a missing `status` key; it is now explicitly `split`, as required for a definition.
The corrected packet passed the required `deliver2.py --no-push` dry run:
`OK (dry run): commit e87b78d8145 passes the preflight and compiles; nothing pushed`.
The final delivery reruns these checks before pushing.
