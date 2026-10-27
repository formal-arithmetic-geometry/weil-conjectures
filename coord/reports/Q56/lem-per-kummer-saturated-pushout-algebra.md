## Worker report

The module `Sheaf.AlgebraicGeometry.KummerSaturatedPushoutAlgebra` states
`AlgebraicGeometry.kummer_saturated_pushout_algebra`. Its only postponed proof is
this theorem, with all sixteen DAG proof steps and their dependency citations in
its docstring. All helper definitions have actual data. The item's statement,
proof, dependency lists, and every field other than `lean` are unchanged.

The node uses additive notation. This module consistently uses multiplicative
notation, matching `IsFineSaturatedMonoid` and the recorded log interfaces:
`1` denotes zero, multiplication denotes addition, and `s ^ m` denotes `m s`.
This permits torsion and units; no sharpness or torsion-freeness is assumed.

Hypothesis and clause audit:

| Node text | Lean rendering |
| --- | --- |
| Fine saturated commutative monoids P,Q,R | Explicit `P Q R : Type u`, `[CommMonoid ...]`, and `hP`, `hQ`, `hR : IsFineSaturatedMonoid ...`. The recorded predicate means finite generation, injectivity into the actual group completion, and positive-root closure there. |
| Injective h, with positive multiples of every q in its image | `h : P →* Q`, `hinj : Function.Injective h`, and `hkum : ∀ q, ∃ d p, 0 < d ∧ q ^ d = h p`. |
| Any homomorphism a | `a : P →* R` with no additional condition. |
| Injective group completion map | `hgp`, using `Algebra.GrothendieckGroup.lift (of.comp h)`. |
| Finite cokernel C killed by n ≥ 1 | `C` is written directly as `GrothendieckGroup Q ⧸ (lift (of.comp h)).range`. `hfinite : Finite C`, `n : ℕ`, `hn : 0 < n`, and `hann : ∀ c : C, c ^ n = 1`. No arbitrary group is substituted for the canonical cokernel. |
| Ordinary pushout quotient S₀ | `KummerPushout.relation` is `conGen` of exactly `(h p,1) ~ (1,a p)` on `Q × R`; `Raw` is its actual quotient. `rawLeft`, `rawRight` are the quotient inclusions. |
| Integralization is the image in S₀^gp | `integralization` is `MonoidHom.mrange` of `GrothendieckGroup.of` on `Raw`. |
| Saturation is the displayed positive-root subset | `saturation.carrier` is precisely `{g | ∃ m : ℕ, 0 < m ∧ g ^ m ∈ integralization h a}`. Its closure proofs use common positive multiples. `Sat` abbreviates this submonoid, and `toSat` is the actual completion map with codomain restricted to it. |
| S is fs | First conjunct `IsFineSaturatedMonoid (Sat h a)`. |
| R → S is injective | `Function.Injective (right h a)`, where `right = toSat.comp rawRight`. |
| R^gp → S^gp is injective | Injectivity of the explicit completion lift of `right`. |
| Every s has a positive multiple in R | `∀ s : Sat h a, ∃ m r, 0 < m ∧ s ^ m = right h a r`. |
| The canonical cokernel is C | The existential multiplicative equivalence from `S^gp / range(R^gp)` to `C`, normalized on every element coming from `Q`. Those elements generate the quotient group, so this specifies the canonical equivalence. |
| Pushout among fs monoids | For every `T : Type v`, commutative monoid structure and `IsFineSaturatedMonoid T`, and every compatible `f : Q →* T`, `g : R →* T`, there exists exactly one extension `l : Sat h a →* T` restricting to f and g. The two canonical legs commute by their quotient construction. The test-monoid universe is independent of u. |
| Z[M] with its prescribed basis and multiplication | The existing `MonoidAlgebra ℤ M` and `MonoidAlgebra.of ℤ M`. No replacement ring or uninterpreted basis is introduced. |
| Every commutative Z[R]-algebra A with n invertible | `AlgebraRealization.{u,v}` universally quantifies `A : Type v`, `[CommRing A]`, `[Algebra (MonoidAlgebra ℤ R) A]`, and `IsUnit (n : A)`. The coefficient universe is independent of u. |
| First displayed map is finite and surjective on spectra | The actual `Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[ℤ[R]] ℤ[S]` is `Finite`, and `PrimeSpectrum.comap` of it is surjective. These are the underlying maps of the scheme spectra. |
| Second displayed map is finite and surjective on spectra | A ring homomorphism from the actual `A ⊗[ℤ[R]] ℤ[Raw h a]` to the actual `A ⊗[ℤ[R]] ℤ[Sat h a]`, specified by `b ⊗ z^s ↦ b ⊗ z^(toSat s)` for every b and s, is `Finite` and has surjective `PrimeSpectrum.comap`. These tensor monomials additively generate, so the specification determines the canonical map uniquely. No unconstrained comparison map is used. |
| After arbitrary further scalar extension | The coefficient algebra quantifier includes every A′ with its composite Z[R]-algebra structure. For any A → A′ the canonical tensor reassociation identifies the base-changed maps with exactly the two formulas asserted for A′ (DAG Step 11). No restriction to flat or finite type scalar extensions occurs. |
| Fs log structures on arbitrary schemes and compatible P,Q,R charts | `LogRealization` quantifies arbitrary `Scheme.{u}`, `EtaleLogStructure`, and `IsFineSaturated`, with the recorded arbitrary-scheme `EtaleLogMap` and `ChartCospan`. That structure consists of three genuine `IsChart` charts whose maps agree with h,a under the given log morphisms. It contains no Noetherian condition. |
| Ordinary fibre product F and its map to Spec Z[S₀] | F is literally `pullback f.base g.base`. Its prelog map χ is specified on the images of both Q and R by the structural charts and the ordinary projections. This determines χ on the quotient pushout. `F.toSpecΓ ≫ Spec.map (MonoidAlgebra.lift ... χ)` is the corresponding canonical scheme map; no affineness of F is imposed. |
| Displayed saturated chart scheme | `ChartScheme h a F χ` is literally the scheme pullback of that map and `Spec.map (MonoidAlgebra.mapDomainRingHom ℤ (toSat h a))`. `chartToBase` and `chartToSpec` are its actual projections. |
| Associated S log structure | `chartBeta` is the pullback of the actual S monomials along `chartToSpec`, using `Scheme.ΓSpecIso`. `LogRealization` asserts `IsAssociatedLogPresentation chartBeta L η` with `L.IsFineSaturated`. It reuses the recorded quotient-presheaf sheafification characterization, not an arbitrary chart homomorphism. |
| Compatible maps of the three log sheaves and fs fibre-product property | The two log legs p,q have the prescribed scheme projections, take the original Q,R charts to the images of `left`, `right` in the associated S chart, and have a common composite to M. For every fs test log structure and compatible cone, the final `∃! b` gives its unique log morphism to L, using `EtaleLogMap.CompEq` (base maps and every relative étale section map). |
| Commutes with restriction of charts | `Restricts` requires the same explicit chart construction after every étale restriction U → F, with an associated fs log structure and a strict étale comparison to L. Its base map is fixed by both pullback projections; its log map is fixed on every S chart element. Arbitrary changes of compatible charts also preserve the characterized object by uniqueness of the stated fs universal property. |
| Existence of compatible charts locally | `CompatibleLocalCharts` quantifies an arbitrary fs log morphism g, geometric point y, prescribed pointed target étale neighbourhood W,w and fs chart B on W. It gives a pointed source étale neighbourhood V,v, a map k:V→W with both the scheme square and point-lift equation, an fs monoid D and genuine chart r on V, and a:B→D satisfying `(g.sectionMap ...).comp c = r.comp a`. The prescribed target chart and geometric point are retained. |
| No Noetherian or flatness assumptions | No `[IsLocallyNoetherian ...]`, `[IsNoetherianRing ...]`, flatness, nontriviality, or finite type assumptions occur. In particular the locally Noetherian bundled `FineSaturatedLogScheme` is never used as a test object. |

Dependency interfaces read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtaleLogStructure`,
  `EtaleLogStructure.IsChart`, `EtaleLogStructure.IsFineSaturated`, and the stalk
  conventions; its imported `Sheaf.AlgebraicGeometry.LogRegularPair` defines
  `AlgebraicGeometry.IsFineSaturatedMonoid` with the canonical completion.
- `Sheaf.AlgebraicGeometry.LogIdealChartPresentation`: `EtaleLogMap`, its
  relative étale `sectionMap` and compatibility, `EtaleLogMap.CompEq`, and
  `EtaleLogMap.IsStrictEtale`. The existing tensor-chart definitions were also
  read; their common-universe specialization is not imposed on the coefficient
  algebras here. The algebra clause directly uses Mathlib's tensor product.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, the quotient
  construction and `⊗ₜ`; `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`:
  actual tensor ring structures and `Algebra.TensorProduct.includeLeftRingHom`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Scheme.toSpecΓ` and
  `Scheme.ΓSpecIso`; `Mathlib.AlgebraicGeometry.Pullbacks`: scheme pullbacks and
  the recorded `pullbackSpecIso` proof input.
- `Sheaf.AlgebraicGeometry.IntegralChartLogificationThickening`:
  `integralChartLogificationThickening`; its imported associated-log module gives
  `associatedLogPresheaf`, `associatedLogIota`, `IsAssociatedLogPresentation`.
- Proof imports: `Sheaf.GroupTheory.FineMonoidFiniteSaturation`
  (`fine_monoid_finite_saturation`), `Sheaf.TraceFormula.FsFaceSharpening`
  (`AlgebraicGeometry.face_sharpening`),
  `Sheaf.AlgebraicGeometry.AssociatedLogArbitraryScheme`
  (`EtaleLogStructure.integral_saturated_of_isFineSaturated`),
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` (`AlgebraicClosure`),
  `Mathlib.Algebra.Category.Grp.Injective` (`Module.Baer.of_divisible`, with
  `Module.Baer.extension_property_addMonoidHom` from its imports).
  The prelog-stalk-chart-spreading node has no recorded declaration in the read
  snapshot; no invented import is supplied. Its proof input remains explicitly
  cited in the theorem's natural-language proof.

Source reading: ILO PDF pp.77–78 (printed VI pp.71–72), pp.113–114 (printed
VIII pp.107–108), and pp.152–153 (printed X pp.146–147), read with `pdftotext`.
The source defines Kummer by injectivity and root cofinality, describes standard
Kummer covers by these monoid algebras and invertible annihilator, and takes
saturated chart base changes in fs log schemes. The full explicit algebraic and
arbitrary-scheme refinements are the unchanged agent-formulated DAG statement
and its proof, as identified in that source record.

Edge cases checked before and during the clause audit:

- All three monoids trivial, and h the identity with any a: the saturation and
  cokernel reduce correctly; the ordinary and saturated chart constructions
  reduce to the unchanged base chart.
- In additive notation P=Q=N with h multiplication by d>0 and R=0: the saturation
  contains the finite torsion group Z/d. The statement preserves this torsion;
  the cokernel and the group-algebra spectrum clauses remain meaningful.
- Pure groups, including finite unit groups: root closure does not discard
  units or require torsion-freeness. Positive exponents include 1.
- The annihilator n=1 is allowed, while n=0 is excluded by `hn` as in the node.
- The zero ring A is allowed: both spectra are empty and the surjectivity
  assertions are true. Rings of positive characteristic and nonflat algebras
  are included whenever the specified n is a unit.
- Empty schemes and empty étale chart domains are included. The chart and point
  clauses use universal quantification over geometric points; no nonempty chart,
  scheme, spectrum or index assumption is imposed.
- No cancellation of Raw is assumed: integralization is its actual image, so
  relations lost under group completion are handled before saturation.
- The canonical F→Spec Z[S₀] uses the global-sections adjunction, so arbitrary
  nonaffine charted schemes are included.
- Coefficient rings and fs monoid tests have independent universe v; geometric
  log tests retain the universe convention of the recorded small étale site.

Searches for an existing statement (all msearch results are also in the sandbox's
`searches.jsonl`):

1. `msearch.py ... leanfinder "saturated pushout fine saturated Kummer monoids finite monoid algebra"`:
   eight hits, headed by `MonoidAlgebra.instIsPushout`, `.instIsPushout'`, and
   finite-type/finite-generation monoid-algebra lemmas. These concern scalar
   pushouts or finite type, not saturated monoid pushouts or fs log products.
2. `msearch.py ... loogle "Algebra.GrothendieckGroup, MonoidAlgebra"`: no hits.
3. `msearch.py ... grep "Kummer|saturatedPushout|monoidPushout"`: 25 hits,
   ordinary number-theoretic Kummer material, no matching logarithmic theorem.
4. `msearch.py ... leansearch "pushout of fine saturated monoids"`: eight hits,
   mostly `Monoid.PushoutI` and category pushout existence. `Monoid.PushoutI`
   uses the ordinary noncommutative coproduct construction and does not state
   saturation, finiteness, or the log-scheme clauses.
5. `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for the node id, `saturatedPushout`,
   `kummerPushout`, `kummer_saturated_pushout_algebra`, and `namespace KummerPushout`:
   no exact match. Related existing fine-saturation, associated-log and
   log-ideal-chart declarations were opened and reused as listed above.
6. `tools/blueprint_refs.py search "saturated pushout"`: no blueprint node match.
   `tools/blueprint_refs.py ancestor` reports `lem-per-artin-gabber-affine-curve`;
   no new node is needed because all helpers construct or spell out notions
   already introduced in this item's own statement.

No statement correction, disputed statement, new definition node, or dependency
replacement is needed. Definitions are explicit and the only sorry is the main
theorem. Server compilation is through `scompile.py` only.

## Second reading by Q56

A separate pass over the completed file and the unchanged node checked the
hypotheses and every conclusion against the table above. This is the worker's
clause audit; the maintainer supplies the independent review after delivery.

The audit caught and repaired three concrete interface issues before delivery:
(1) the chart map from a nonaffine F must use `F.toSpecΓ`, not a morphism whose
source is Spec Γ(F); (2) identity test-object equations need explicit category
identity equalities to avoid unresolved étale-site universe metavariables;
(3) restriction must fix the map on all S chart elements, in addition to fixing
both scheme projections and strictness. The completed `chartBeta`, `ChartCospan`,
`LogRealization`, and `Restricts` include these corrections.

Re-read the quotient relation, integralization, root subset and normalized
cokernel equivalence against the original formulas; the construction keeps
finite torsion. Re-read both actual tensor rings and the tensor-monomial
formula; neither ring is replaced by an abstract finite algebra. Re-read the
fs test cone quantification and the prescribed pointed target chart: neither
Noetherianness nor a changed target chart is smuggled in. The theorem docstring
retains every proof step for stage 3. The node copy changes only `lean`.
