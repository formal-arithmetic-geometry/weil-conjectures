## Worker report

Stage 2, group Q126, item lem-trf-scheme-galois-comparison-normal-form.
The new module Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm states exactly one
named theorem, WeilConjectures.FiniteFieldDatum.schemeGaloisComparison_normal_form,
with proof `sorry`. There are no new definitions, dependency modules or statement changes.
The node copy changes only `lean`.

The previous worker's blocker was a stage confusion. The Q118 merge at ledger line
26957 is explicitly reported in coord/reports/Q118/lem-trf-scheme-galois-comparison-normal-form.md
as a stage-1 split with no Lean attachment. The live node has no `lean` or reviewed_lean
record and no repair note. Its accepted stage-1 split is preserved byte for byte outside
`lean`; this stage-2 statement does not redeliver or alter that split.

Clause-by-clause rendering:

- The prime p, positive a, q=p^a, finite field k_0 with q elements and fixed algebraic
  closure k are the existing `D : WeilConjectures.FiniteFieldDatum.{u}`. Its fields
  `prime`, `exponent_pos`, `cardinality_eq`, `card_base`, `field_base`, `finite_base`,
  `algebra_closure`, and `isAlgClosure` carry precisely these data.
- X_0 is `X₀ : Over (Spec (CommRingCat.of D.k₀))`. Finite type is rendered by
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]`. Its geometric fibre X is
  `(D.geometricFiber X₀).left`, the existing base change, not an arbitrary scheme.
- Phi, its m-th power, arithmetic sigma and inverse geometric g are the recorded
  `schemeFrobenius`, `schemeFrobeniusIterate`, `arithmeticGaloisFrobenius`, and
  `geometricGaloisFrobenius`. The latter two are the inverse and hom of the same
  `geometricFrobenius` scheme isomorphism. A geometric Galois power is explicitly
  `HPow.hPow (α := End (D.geometricFiber X₀).left) (D.geometricGaloisFrobenius X₀) m`.
- R is `(R : Type u) [CommRing R] [Finite R]`. The stated annihilator is
  `hR : ∃ n : ℕ, IsUnit (n : D.k) ∧ ∀ r : R, n • r = 0`, exactly the coefficient
  hypothesis of the recorded specified-comparison declaration. This is equivalent
  to annihilation by an integer prime to p: k has characteristic p, so a natural
  integer is a unit in k exactly when p does not divide it. Taking absolute values
  handles signed integers. Conversely that positive natural represents an integer.
  There is no invertibility condition on R, no selected coefficient prime, and no
  nonzero-ring assumption. In particular R=0 admits annihilator n=1.
- `m : ℕ` and `hm : 1 ≤ m` render every positive iterate, including m=1. No bound
  on m, no divisible-by-a condition, and no perfection of X are imposed.
- The conclusion `∃ hX : (D.geometricFiber X₀).left.IsCharacteristic D.p` is the
  asserted characteristic, with the dependency's prime-and-every-open definition.
  It is a conclusion rather than a hypothesis. `hX.2 ⊤` supplies the proof required
  by the upstream `iterateFrobenius`; proof irrelevance makes this independent of
  which proof of characteristic is obtained.
- H=F_X^(am) is the upstream `iterateFrobenius D.prime (hX.2 ⊤) (D.a * m)`.
  The witness `w : Phi^m = H ≫ g^m` is Phi^m=g^m composed with H; the next equality
  `Phi^m = g^m ≫ H` is the other factorization. These are ordinary Scheme Hom
  equalities. There is no Over-Spec(k) structure or k-linearity requirement on g.
- D_R is represented by the recorded comparison's own `proEtaleDerivedCategory X R`,
  the ordinary unbounded derived category of modules over the sheafified constant
  ring with the canonical `ULift` coefficient convention. The project's finite
  coefficient interface is also imported. Its continuous-function sheaf and its
  constant-scalar realization give the standard alternative presentation of these
  finite coefficient modules; neither constructibility nor boundedness is assumed.
  The statement is on the same category as `canonicalSchemeGaloisComparison`.
- The left side is the actual specified positive-iterate map
  `(D.canonicalSchemeGaloisComparison X₀ R hR m hm).hom.app K`, selected from the
  full comparison theorem together with its multiplicativity and normalizations.
  No arbitrary comparison or hypothesis of the desired equality is supplied.
- `d_R` is the first two factors on the right: the component of `eqToHom` along
  `w`, followed by `(proEtaleConstantRingPullbackComposition H (g^m) R).inv.app K`.
  This compositor is definitionally the selected general canonical comparison,
  with its canonical constant-section composite-coefficient equality transported.
  Its inverse has exactly the direction L(Phi^m)^* -> LH^* L(g^m)^*. The transport
  is indispensable because the two underlying scheme maps are propositionally equal.
- The last factor is `proEtaleFrobeniusDerivedIso R` of the tau family selected from
  `absoluteFrobenius_proEtale_trivialization D.p D.prime R`, at X, hX, and the single
  exponent `D.a * m`. The theorem's first chosen site map is fixed by the relative
  Frobenius projection equation; its chosen module tau is fixed by its adjunction
  unit on every section. Thus these choices determine the maps up to equality,
  and are permitted selections of normalized canonical data. No hollow data or
  mere Nonempty choice is introduced. This is exactly the cited site's tau,
  rather than an arbitrary iterate-compatible isomorphism.
- Finally `∀ K : proEtaleDerivedCategory X R` evaluates this tau at
  `(proEtaleConstantRingDerivedPullback R (g^m)).obj K`. Together the factors render
  kappa_(R,K)^(m)=tau_(R,L(g^m)^*K)^(am) composed with d_(R,K). The equality is of
  the actual derived morphisms, not merely their cohomology maps or existence of
  an isomorphism.

Dependency declarations read and reused:

- Sheaf.Paper.FiniteFieldFiber: WeilConjectures.FiniteFieldDatum and
  WeilConjectures.FiniteFieldDatum.geometricFiber.
- Sheaf.SixFunctors.SchemeFrobenius: WeilConjectures.FiniteFieldDatum.schemeFrobenius,
  schemeFrobeniusIterate, arithmeticGaloisFrobenius and geometricGaloisFrobenius.
- WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius:
  AlgebraicGeometry.Scheme.iterateFrobenius and its sectionwise power formula.
- Sheaf.AlgebraicGeometry.SchemeCharacteristic: AlgebraicGeometry.Scheme.IsCharacteristic.
- Sheaf.AlgebraicGeometry.ProEtaleFiniteModules:
  AlgebraicGeometry.ProEtale.FiniteCoefficientModules,
  FiniteCoefficientDerivedCategory, finiteCoefficientRealization, and the latter's
  equivalence for arbitrary finite rings. The comparison itself uses the existing
  constant-ring model AlgebraicGeometry.Scheme.proEtaleDerivedCategory of
  Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory.
- Sheaf.Paper.IntegralFinitePullbackComposition:
  WeilConjectures.integralTowerGeneralPullbackComposition, the unchanged alias of
  AlgebraicGeometry.Scheme.proEtaleCanonicalPullbackComposition. Its constant-ring
  specialization is AlgebraicGeometry.Scheme.proEtaleConstantRingPullbackComposition
  in Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison. I read its full
  body and normalization equality: it specializes that canonical comparison and
  transports only the canonical coefficient-identification equality.
- Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite:
  AlgebraicGeometry.Scheme.absoluteFrobenius_proEtale_trivialization and
  AlgebraicGeometry.Scheme.proEtaleFrobeniusDerivedIso. The latter is exact termwise
  derived descent of the former's module isomorphism, followed by the derived
  identity comparison.
- Sheaf.SixFunctors.SelectedSchemeGaloisComparison:
  WeilConjectures.FiniteFieldDatum.canonicalSchemeGaloisComparison; its public
  dependency Sheaf.SixFunctors.SchemeGaloisComparison supplies schemeGaloisComparison,
  including the actual normalized iterate family and multiplicativity.
- Proof inputs are imported without `public`: FrobeniusFactorization,
  FrobeniusTrivializationPullback, ProEtaleDerivedPullbackCoherence,
  ProEtaleConstantRingComposition and ProEtaleConstantRingMap. Their declarations
  supply the two factorizations, arbitrary-pullback/addition laws, canonical
  compositor coherence and constant-section coefficient convention.

I read the node's six-step proof and the source
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-sf-rf-shriek-preservation/prop-trf-scheme-galois-comparison.proof.md.
The complete six-step proof is rendered in the theorem docstring; stage 3 is left
exactly one matching named sorry. No statement is disputed and no node fault was found.

Edge cases checked: m=1 is explicitly allowed and gives the defining normalization;
a=1 uses exponent m; m=2 is the first multiplicativity step; empty X has zero section
rings and satisfies the existential characteristic conclusion; R=0 is allowed;
X_0=Spec(k_0) has the required semilinear Galois action; a nonreduced affine model
uses the same power maps without assuming Frobenius invertible on schemes. There
is no boundedness, finite Tor amplitude, smoothness, etaleness, nonemptiness or
constructibility condition on K or X. All universe variables and parameters are
explicit and `autoImplicit` is false. No local notation or instances occur.

Searches, all executed through the prescribed msearch.py wrapper or read-only rg:

- LeanFinder: "The specified multiplicative scheme Frobenius and geometric Galois
  comparison is the canonical pullback compositor followed by the absolute
  Frobenius trivialization at exponent a times m". Eight hits, including WittVector
  isocrystal Frobenius and Scheme.Modules.pullbackComp; none states the site-derived
  comparison with these coefficients and this normalization.
- Loogle: `"frobenius", "pullback"`. One hit,
  CategoryTheory.Regular.frobeniusMorphism_isPullback; this is a regular-category
  subobject theorem, not a scheme-derived comparison.
- Mathlib grep under AlgebraicGeometry:
  `(schemeGalois|SchemeGalois|[Ff]robenius.*trivial|trivial.*[Ff]robenius)`: zero hits.
- LeanSearch: "The specified positive iterate scheme Frobenius geometric Galois
  derived pullback comparison equals canonical composition followed by the absolute
  Frobenius trivialization". Eight hits, all field/ring iterated-Frobenius formulas;
  none is the requested natural-transformation normal form.
- rg of lean/WeilConjectures and lean/Sheaf for canonical Frobenius trivialization,
  choose_spec paths and scheme/Galois comparison found the recorded dependencies,
  coefficientFrobeniusTrivialization, and a private canonicalComparison_normalization
  helper in SchemeGaloisPullbackNaturality. That helper is private, uses `let`
  binders and does not state characteristic or both factorizations; it cannot be
  the existing public declaration for this node. Its section-unit uniqueness
  argument confirms that the specified tau is independent of witness selection.
- rg for the blueprint id in lean/WeilConjectures and lean/Sheaf returned no hits;
  rg for schemeGaloisComparison_normal_form in those directories, Mathlib and
  dag/lean_names_upstream.json also returned no hits.

## Second reading by Q126

I reread the node and the module clause by clause after drafting. This is a second
pass by this worker, not a claim of an independent agent review: this dispatcher
brief explicitly forbids starting other agents; the maintainer independently
reviews the delivery. I verified both Scheme Hom equalities with categorical
composition order, checked the exact source and target of each of the three
morphism factors, and confirmed that the selected kappa has multiplicativity,
while the selected tau is fixed on site projections and module sections. I kept
the annihilator condition identical to the recorded canonical comparison, which
is equivalent to the node's prime-to-p condition. I checked that the characteristic
proof is obtained in the conclusion, so it excludes neither the empty scheme nor
any model allowed by the source. The whole statement has no `let` or hidden `show`
binders. The first compile exposed only a line-break parser error in a projection
chain; this was repaired by breaking before the theorem arguments instead. There
are no private copies of definitions and no extra mathematical assumptions.

## Validation

Every compilation uses scompile.py, on the server against the published build.
scompile.py compiled both the sandbox and library module cleanly, in 16.4 and
19.5 seconds respectively, with no errors or warnings. The first delivery dry run
returned `OK (dry run): commit 90c03263cd2 passes the preflight and compiles; nothing
pushed`. Before the final dry run I expanded the last two proof-docstring steps to
retain the explicit interchange, two naturality equations, addition law and induction
from the node, and made no change to the compiled signature. The delivery wrapper
repeats the compile and preflight for that final text.
