## Worker report

The delivery states all clauses of `lem-sfb-square-zero-periodic-tensor` in
`Sheaf.Paper.SquareZeroPeriodicTensor`. No mathematical statement or dependency list
was changed. The two theorems have `sorry` proofs; the sole helper definition has
actual data. There are no new DAG nodes and no disputed statements.

The source read is the current main-20261015 blueprint file
`sec-proetale-coefficients/sk-def-localizing-closure/sk-def-localizing-closure-ctf-equals-bc.proof.md`,
“The examples”. Its periodic resolution over Z/ell² is exactly the special case
R = Z/ell², t = ell of the node's general annihilator hypothesis. The node's seven
proof steps were read in full; the docstrings give the ordinary and sheaf parts of
that plan, including both resolution-independence inputs.

Hypotheses and clauses, matched to Lean:

| Node text | Lean rendering |
| --- | --- |
| R is a commutative ring | `(R : Type r) [CommRing R]` in both theorems; the zero ring is allowed. |
| t belongs to R and t² = 0 | `(t : R) (ht : t ^ 2 = 0)`. |
| Ann(t) = tR | `hann : ∀ a : R, t * a = 0 ↔ a ∈ Ideal.span ({t} : Set R)`. Since R is commutative, the span is exactly the principal ideal tR. |
| F = R/tR | Every ordinary occurrence is `R ⧸ Ideal.span ({t} : Set R)`, as its natural R-module. |
| The augmented sequence is a free resolution | `ModuleCat.square_zero_periodic_resolution_tensor` asserts existence of a `ProjectiveResolution` of F together with `e : ∀ n : ℕ, P.complex.X n ≅ ModuleCat.of R R`. These isomorphisms say every term is the free rank-one module, rather than only an unspecified projective module. |
| Every displayed differential is multiplication by t | `∀ n x, (e n).hom (P.complex.d (n+1) n x) = t * (e (n+1)).hom x`. This is the chain indexing q = -i of the displayed nonpositive cochain resolution. |
| The augmentation is the quotient R → F | `∀ x, P.π.f 0 x = Ideal.Quotient.mk (Ideal.span {t}) ((e 0).hom x)`. `ProjectiveResolution.quasiIso` gives the required exact augmentation, including surjectivity and the kernel at degree zero. |
| Tor_q(F,F) ≅ F for every q ≥ 0 | The second conjunct is `∀ q : ℕ, Nonempty ((((Tor (ModuleCat R) q).obj F).obj F) ≅ F)`, with F written out. This is Mathlib's left-derived ordinary tensor, not a newly defined Tor. |
| H^(-q)(F tensor-derived F) ≅ F | The third conjunct uses `DerivedCategory.homologyFunctor (ModuleCat R) (-(q : ℤ))` applied to the tensor of the two `DerivedCategory.singleFunctor` images of F. The derived monoidal structure is the existing K-flat construction; q ranges over all naturals. Both equivalent forms are included explicitly. |
| Every scheme V, with its small pro-etale site | `(V : Scheme.{u})`, with `ProEt.topology V`; no nonemptiness, Noetherian, connectedness or finite-coefficient assumption occurs in the isomorphism clause. |
| Constant R_V and F_V, with the quotient scalar action | The base ring is `(constantSheaf (ProEt.topology V) CommRingCat).obj (CommRingCat.of (ULift R))`, with commutativity forgotten. `squareZeroQuotientModule R t V` is the unit module over the constant quotient ring sheaf, restricted along the constant image of `RingHom.ulift (Ideal.Quotient.mk (Ideal.span {t}))`. This is precisely the canonical constant F-module and its R_V-action. The helper uses the existing constant-ring restriction construction; it makes no arbitrary choice of an action or morphism. |
| H^(-q)(F_V tensor-derived F_V) ≅ F_V for every q ≥ 0 | The first conjunct of `AlgebraicGeometry.Scheme.square_zero_periodic_tensor` uses `SheafOfModules.ringedSiteDerivedTensorOfUniverses` on the two degree-zero images of `squareZeroQuotientModule R t V`, followed by `DerivedCategory.homologyFunctor` in degree `-(q : ℤ)`, and states a sheaf-module isomorphism with that same F_V. |
| If F ≠ 0 and V nonempty, all these sheaves are nonzero | The second conjunct is conditional on `Nontrivial (R ⧸ Ideal.span {t})` and `Nonempty V` and concludes both `¬ IsZero F_V` and `∀ q : ℕ, ¬ IsZero H^(-q)(F_V tensor-derived F_V)`. This uses categorical zero for sheaves, not zero of their underlying type. |

The ring universe r and scheme universe u are independent. The coefficients and
module sections are placed in `max r (u+1)` using `ULift.{u+1}` and the existing
sheafification transports `WeilConjectures.integralCoefficientAbSheafify` and
`WeilConjectures.integralCoefficientAbLocallyBijective`. The site itself retains
object universe u+1 and morphism universe u. The localization universe w is an
explicit `HasDerivedCategory` choice, as in `def-weil-abstract-derived-category`.
It is not a mathematical existence or finiteness assumption. The Abelian structure
is exactly Mathlib's `SheafOfModules.instAbelian`, with those existing sheafification
proofs supplied explicitly; there is no chosen or second Abelian structure.
The same instance and localization are passed explicitly to the two single functors,
the derived tensor, and cohomology. This prevents elaboration from trying to unify
`max r (u+1)` with `u+1` using an older specialized instance. No universe equality is
imposed. No file-local notation, local instance, private declaration, or statement
`let` is used.

Statement dependency declarations read and used:

| DAG dependency | Module and declaration |
| --- | --- |
| `def-pc-kflat-complex` | `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: `CochainComplex.IsKFlatIndependentCoefficients`, `CochainComplex.IsKFlatResolutionIndependentCoefficients`; the intrinsic tensor uses this existing resolution predicate. |
| `def-weil-abstract-derived-category` | `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.singleFunctor`; cohomology is `DerivedCategory.homologyFunctor` from `HomologySequence`. |
| `def-weil-pbc-proetale-site` | `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, `AlgebraicGeometry.Scheme.ProEt.topology`. |
| `def-weil-pbc-constant-sheaf` | `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, defined as constant presheaf followed by sheafification. |
| `def-weil-derived-tensor` | The landed record remains NE's `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`, `AlgebraicGeometry.ProEtale.derivedTensor`. For this intrinsic consumer the existing `Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses`, `SheafOfModules.ringedSiteDerivedTensorOfUniverses` is used directly, as permitted by the landed record's note; see the item's `lean.note`. |

The other proof-dependency modules are imported, without `public`, as required for
stage 3: `WeilConjectures.Algebra.Homology.BoundedFlatKFlat`;
`Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`;
`Mathlib.Algebra.Homology.BifunctorShift`;
`Sheaf.CategoryTheory.FiniteTypeConstantExact`;
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`;
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`;
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`;
`Sheaf.Algebra.Homology.DerivedTensorResolutionIndependent`;
`Sheaf.CategoryTheory.SiteConstantModuleUnit`.
Their node records and relevant declarations were read, including the constant
module unit, exactness, total tensor and resolution-comparison descriptions.
`Mathlib.CategoryTheory.Monoidal.Tor` supplies `CategoryTheory.Tor`;
`Mathlib.Algebra.Category.ModuleCat.Projective` supplies the module projectivity
infrastructure. The ordinary derived tensor uses the existing
`DerivedCategory.hasDerivedMonoidalCategory`, `ModuleCat.hasFunctorialFlatResolution`
and derived monoidal instances, with no custom tensor operation.

Edge cases checked before finalizing:

- q = 0 is included in both natural-number quantifiers. The outgoing differential
  is zero and the tensor's degree-zero homology is F, not a claimed vanishing.
- R = 0 satisfies both algebraic hypotheses and gives the zero resolution and zero
  sheaves; no `Nontrivial R` is assumed. The conditional nonvanishing does not apply.
- t = 0 with nonzero R fails `hann` (at a = 1), correctly excluding the false
  periodic-exactness case. If F = 0, the isomorphisms still assert zero objects and
  the nonvanishing antecedent is false.
- R = Z/4, t = 2 and R = k[e]/(e²), t = e satisfy exactly the square-zero and
  annihilator conditions. Tensoring the displayed resolution has zero differential
  and one copy of F in every degree q ≥ 0.
- The empty scheme is allowed by the sheaf isomorphism clause. Its sheaves are zero,
  and `Nonempty V` prevents a false nonvanishing conclusion. Disconnected schemes
  are allowed; no connectedness assumption entered the statement or proof outline.
- The natural-number free resolution corresponds to the entire nonpositive
  cochain complex and has no finite-length or positive-degree truncation condition.

Searches for an existing exact statement and helper:

- `msearch.py ... leanfinder`, query: “For a commutative ring R and square zero element
  t with annihilator t equal to tR the quotient has a periodic free resolution and Tor
  of R/t with itself equals R/t in every degree”. Eight hits included generic
  `CategoryTheory.isZero_Tor'_succ_of_projective`, `Rep.isZero_Tor_succ_of_projective`
  and formal smoothness lemmas; none state this result.
- `msearch.py ... loogle`, query: `"Tor", "quotient"`. Twelve hits were quotient-ring
  maps and quotient commutativity infrastructure, not the self-Tor calculation.
- `msearch.py ... grep`, query: `square.?zero|periodic`, directory `Algebra/Homology`.
  Two hits in `Mathlib/Algebra/Homology/AlternatingConst.lean`. The full construction
  `HomologicalComplex.alternatingConst` and its homology interfaces were opened:
  these define general periodic complexes, but do not give this quotient resolution,
  its self-Tor, the pro-etale calculation or nonvanishing.
- `rg -n 'square.zero|periodic'` in `lean/WeilConjectures` and `lean/Sheaf`, followed
  by targeted searches in their homology and Paper directories. Hits were unrelated
  square-zero lifting, homological differential equations, the specific finite-ring
  examples in `LocalizingClosureCtfEqualsBc`, and the varpi^n/varpi adic calculation
  in `LevelwiseAdicTruncations`. The latter two files were opened; neither states the
  arbitrary commutative-ring/exact-divisor assertion of this item.
- `rg -n 'lem-sfb-square-zero-periodic-tensor' lean/WeilConjectures`: no hits.
- Exact-name searches for `square_zero_periodic_tensor` and
  `squareZeroQuotientModule` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no existing declarations. The constant quotient
  helper is only the specific canonical scalar restriction needed by this node,
  assembled from the recorded constant sheaf and derived-tensor scalar restriction;
  it is not a new general definition of constant sheaf or sheaf tensor.

Validation: the complete module was compiled through `scompile.py` on the server,
against the live published library. Only that prescribed wrapper was used; no
local/global Lake build or direct repository mutation was performed. The required
`deliver2.py --no-push` and final delivery results are checked after this report.

## Returned-delivery repair

The independent review of immutable head `8b91eda4e3a4` found only an unnecessary
rebind of `def-weil-derived-tensor` (H13); it accepted the item's mathematical
statement and module. The saved packet's initial dry run passed at `8e0e83423dd`,
but still contained that rebind, so the requested repair was applied:

- Removed `dag/nodes/sec-picard-framework/def-weil-derived-tensor.json` from the
  delivery. NE's 2026-10-18 landed `existing: true` fixed-ring tensor binding stays
  unchanged, including its explicit permission to use the intrinsic construction
  for intrinsic consumers.
- Added `lean.note` on this item explaining its direct use of the existing intrinsic
  tensor with independent ring and scheme universes. No dependency module or new
  node is delivered, and no dependency record is rebound.
- Retained `lean/Sheaf/Paper/SquareZeroPeriodicTensor.lean` byte-for-byte from the
  returned packet. Its SHA-256 is
  `973eacf9730a633abde59740fe757ce1b97a55aa23bd48aa816feca38fbe18c7`.
- Compared the item node with current main: only `lean` differs. Its mathematical
  statement, dependencies, proof and all other fields are unchanged. The delivery
  wrapper rebases the packet against current main in its own worktree.

The intrinsic tensor is the already published K-flat total tensor on intrinsic
sheaf modules. It keeps the small pro-etale site object universe u+1 and morphism
universe u, and accommodates coefficient universe max r (u+1). Using it here needs
no change to the fixed-ring dependency's public binding; the review also identified
Q105's Tor-bound item as another direct intrinsic consumer.

Repair validation: `scompile.py Q04 lem-sfb-square-zero-periodic-tensor` compiled
the retained module cleanly (sandbox 7.4 s; library module 5.8 s). Self-checks
confirmed the recorded theorem signature is verbatim, the module SHA-256 is
unchanged, only the item's `lean` field differs from main, and the removed dependency
node is absent from the packet. The prescribed repaired dry run and push follow.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
