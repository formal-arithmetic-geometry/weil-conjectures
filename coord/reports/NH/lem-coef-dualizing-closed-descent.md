## Worker report

Stage 2, group NH, 2026-10-22. The module
`Sheaf.SixFunctors.CoefficientDualizingClosedDescent` states
`WeilConjectures.coefficientDualizingClosedDescent`, with its sole proof `sorry`.
The exported assertion helper `WeilConjectures.CoefficientClosedDescent` is a real
Prop-valued definition assembling the actual canonical constructions and all clauses;
it does not introduce another coefficient category, exceptional functor or scalar map.
The repair adds one definition node owning two existing comparison definitions.
There are no dependency modules, statement corrections, or disputed statements.

The live item's `reviewed` PASS is its stage-1 split, not a Lean review: both `lean`
and `reviewed_lean` were absent. Thus the previous worker's stage-1 live-wins refusal
was inapplicable to this stage-2 task. The accepted split and source text are preserved.
The only item changes are `lean` and three additional statement dependencies:
`def-sf-etale-proetale-ambient-direct-image-comparison` owns the ambient canonical
direct-image mate that appears in the square; `def-weil-pbc-witness-compatibility` owns the actual scalar/site
isomorphism; `def-weil-l-adic-coefficient-extension` owns the coefficient constructions
and their finite positive quotients. No accepted stage-1 proof is split again.

Source read: current main-20261015, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-finite-dualizing.proof.md, paragraph 3, together with the full live item's
expanded proof. Its closed finite-shriek application is precisely the application
whose ordinary descent is stated here. The source's preliminary omega_Y and
compact-support coefficient notation sets up that application; the conclusion uses
M=omega_P, N=I_A M, and the closed ordinary coefficient map, rather than an additional
assertion about the structure-morphism compact-support comparison.

Hypotheses and clauses, read with the helper definition open:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| k is the specified algebraic closure of a finite field of characteristic p | `(D : FiniteFieldDatum.{u})`, with its field, finite-field and algebraic-closure fields |
| ell prime and ell different from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` |
| E is a finite extension of Q_ell, with its valuation ring and uniformizer | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; the existing `Padic.coefficientExtensionRing` uses the recorded integers and uniformizer |
| 1 ≤ m ≤ n; A=O_E/(varpi^n), B=O_E/(varpi^m) | `(m n : ℕ) (hmn : m ≤ n)`, with positive exponents `m+1`, `n+1`; `finiteClosedCoefficient l E n` is exactly the existing A_(E,n+1) |
| Actual quotient A→B | `RingHom.ulift (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)))`, with both ideals explicit; no arbitrary ring map is assumed |
| Y affine, separated and finite type over k | `(Y : Scheme.{u}) [IsAffine Y] (aY : Y ⟶ Spec (.of D.k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]` |
| P=A^r_k and i a closed immersion over k | `AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))`, `[IsClosedImmersion i]`, and `_hi` identifying the composite structure map with aY |
| Ordinary small etale derived categories | `Etale.DerivedCategoryModule` and the literal `DerivedCategory (Sheaf _ (ModuleCat _))` functors; the module value universe is u+1 on both sites |
| F_W,R and its right adjoint G_W,R, omega_W,R=G_W,R R_s | Existing `Etale.rightDerivedLowerShriek`, `Etale.rightDerivedUpperShriek`, `Etale.dualizingComplex`; the theorem's input is the latter for the affine-space structure morphism |
| M=omega_P,A | The final explicit `Etale.dualizingComplex` argument to `CoefficientClosedDescent` |
| I_R is the ordinary closed right adjoint | Body names IA, IB are `Etale.rightDerivedUpperShriek` for the identity-open compactification of i; `adjA`, `adjB` are its ordinary direct-image adjunctions transported by the specified proper forget-supports isomorphism |
| e_R,H is the counit of i_* ⊣ I_R | `adjA.counit.app M`, `adjB.counit.app MB`; these have literal ordinary direct-image sources |
| N=I_A M, M_B=T_P M, T_Y N | Body names `N`, `MB`, `NB` respectively |
| T is ordinary uncompleted derived extension of coefficients | `Te W = ProEtale.pbcFixedScalarExtension W.smallEtaleTopology φ` |
| Bounded constructible finite-Tor vocabulary | Existing `Etale.DerivedCategory.isBoundedConstructible` and `hasTorAmplitudeIn`, read in their owning dependency modules; this explanatory vocabulary in the node adds no assumption on an arbitrary input M: the theorem specializes M to omega_P,A |
| S_W,R=nu^*, U_W,R=Rnu_* and specified eta | `SA`, `SB` use `comparisonUpperStar.mapDerivedCategory`; `derivedComparisonAdjunction.unit.app` is the actual specified eta; U is the comparison lower-star right-derived functor inside `finiteClosedExceptional` |
| J_R=S_Y,R I_R U_P,R | The existing `finiteClosedExceptional`, i.e. `sfFiniteExceptionalFixed` of the identity-open compactification; it is definitionally this composite, not an asserted ambient pro-etale adjoint |
| alpha_R,H=S_Y,R I_R(eta_H) | Body names `αA`, `αB`, the literal maps of the recorded comparison unit |
| B-linear tensor comparison t_W | `(ProEtale.pbcComparisonReduction W φ).symm`; the recorded comparison has the reverse orientation, so this inverse is exactly the node's t |
| delta_R,L is the canonical counit mate | `ProEtale.directImageComparisonAmbient RA i` and its B version, specialized at N and NB; these are constructed by `mateEquiv` of the exact comparison pullback square, whose D+ restriction is `fixedComparisonDirectImageMatePlus` |
| Ordinary c^e and pro-etale c^p are the actual coefficient maps | `Etale.finiteCoefficientDirectImageMap` and `ProEtale.finiteCoefficientChangeDirectImageMap` |
| Normalized coefficient square | The displayed equality starting with `(t P).hom.app (i_* N) ≫ (Tp P).map δA ≫ cpQ`; the other side is `(SB P).map ce ≫ δB ≫ (finiteClosedPush B i).map ((t Y).hom.app N)` |
| Both pro-etale coefficient components invertible | `IsIso cpQ ∧ IsIso cpK`, with Q=SA_Y N and K=J_A(SA_P M), not an arbitrary identification between their pushforwards |
| alpha, delta and kappa identifications are isomorphisms | Explicit `IsIso αA`, `IsIso αB`, `IsIso δA`, `IsIso δB`, `IsIso κ₁`, and the existential proof `hκ₂ : IsIso κ₂` |
| kappa1=Tp_Y(alpha_A,M) t_Y,N | Body name `κ₁ = (t Y).hom.app N ≫ (Tp Y).map αA` |
| kappa2=J_B(t_P,M) alpha_B,MB | Body name `κ₂ = αB ≫ (finiteClosedExceptional B i).map ((t P).hom.app M)` |
| Ordinary c^e is invertible, so its inverse is defined | `∃ hce : IsIso ce`; its inverse is used with that exact proof through `@inv ... ce hce` |
| The ordinary map is uniquely defined by its counit equation | `∃ b : NB ⟶ IB.obj MB`, its displayed ordinary counit equation, and `∀ b', <the same equation> → b' = b`; uniqueness does not assume b' invertible or the site-image formula |
| That very map is an isomorphism | `IsIso b`, in the actual B-linear ordinary derived category |
| Its site image is kappa2^-1 b^pro kappa1 | `(SB Y).map b = κ₁ ≫ finiteClosedShriekMap φ i H ≫ @inv ... κ₂ hκ₂`, with the published counit-normalized pro-etale comparison at H=SA_P M |
| Bounds are independent of b and only those D+ Hom sets are used | Six leading `TStructure.t.plus` conjuncts give bounds on M,N,MB,NB,IB(MB),i_* NB before b is introduced; proof steps 5 and 7 use full faithfulness on NB,IB(MB), then faithfulness on Hom(i_* NB,MB) |
| No preservation of all D+ by T or unbounded pro-etale adjoint | Neither is a hypothesis or conclusion; only the specified objects have individual lower bounds |
| Empty Y, identity reduction, r=0 | No nonemptiness or positive-r condition; counit uniqueness and `IsIso b` include the zero-category case, the quotient with m=n and the affine point |

The helper's `let` expressions occur in the computational body of an exported `def`,
where delta reduction exposes genuine let bindings. They are not let binders in the
signature of a theorem (which elaborate as opaque haves). The main theorem has no
such binders. The helper is only the complete assertion of this node, not a new
independent notion; all geometric, coefficient and derived notions are existing ones.
The existentially obtained arrow is uniquely characterized by the source's counit
identity, so no canonical map is replaced by an unconstrained map or mere Nonempty.

Dependency declarations read and used (including the existing alternative forms):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and coefficient convention.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, with its public coefficient module:
  `Padic.coefficientExtensionRing`, `coefficientExtensionIdeal`, `finite_coefficientExtensionRing`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`, its normalized global form.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` and `...Dualizing`:
  `rightDerivedUpperShriek`, `rightDerivedUpperShriekAdjunction`, `dualizingComplex`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar`:
  `rightDerivedLowerShriekIsoRightDerivedLowerStar`; `Adjunction.ofNatIsoLeft` supplies
  the counit-compatible ordinary closed adjunction, as permitted by the node's I_R notation.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`;
  the normalized compact-support choice is a right adjoint of precisely this functor.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `...QuasiCompact`, `...Separated`, `...Proper`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsProper`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and `...BoundedConstructibleComplexes`:
  `Etale.DerivedCategoryModule`, root `DerivedCategory`, `TStructure.t.plus`,
  `Etale.DerivedCategory.isBoundedConstructible` (not an extra input hypothesis).
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor` and its coefficient vocabulary,
  `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`: `Etale.derivedTensor`,
  `Etale.DerivedCategory.hasTorAmplitudeIn`, `hasTorAmplitudeGE`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparisonModules`;
  its `ProEtale.comparisonUpperStar`, `comparisonLowerStar` are the functors being derived.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its public finite modules:
  `ConstructibleExceptionalCoefficients.System`, recorded `ProEtale.sfFiniteExceptionalAt`;
  this item uses the already published literal finite specialization `sfFiniteExceptionalFixed`.
- `Sheaf.Paper.FiniteClosedShriek`: `finiteClosedCoefficient`, `finiteClosedScalar`,
  `finiteClosedPush`, `finiteClosedExceptional`, `finiteClosedShriekMap`,
  `finiteCoefficientClosedShriek`; no second pro-etale exceptional map is constructed.
- `Sheaf.Paper.FiniteCoefficientDirectImage`: ordinary and pro-etale coefficient maps,
  their `IsFiniteCoefficientDirectImageMap` unique-counit characterizations and isomorphism
  theorems. These specify actual maps independently of arbitrary comparison isomorphisms.
- `Sheaf.Paper.WitnessCompatibility`: `pbcFixedScalarExtension`, `pbcComparisonReduction`;
  the inverse of the latter is the node's B-linear t.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `ProEtale.fixedComparisonDirectImageMatePlus` and its counit normalization.
- `Sheaf.Paper.EtaleProEtaleScalarMate`: `directImageComparisonAmbient`, the mate of the
  exact pullback square; `etaleProEtale_scalar_mate`, the equality used in proof step 2.
- `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport`: `ProEtale.siteClosedCounitTransport`,
  with the normalized identity-open adjunction; the proof plan uses this exact normalization.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`:
  `Etale.compactSupportCoefficientComparisonPlus` and its `CoefficientTensorModel`;
  this is the setup's c_Y,K, not a new compatibility assumption on exceptional functors.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  the generic representative-normalized tensor/pullback interface whose recorded specialization
  gives the scalar/site comparison already used here.
- Proof-only imports: `Sheaf.Paper.FiniteCoefficientFlatModel` for the independent ordinary
  flat-model bound and `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit` for the D+
  comparison unit. The two proof prerequisites `lem-coef-dualizing-closed-chart` and
  `lem-coef-dualizing-closed-site` have no Lean records yet; there is no module to import.
  They remain proof dependencies and are not promoted to assumptions of this statement.

Edge cases checked before and after writing: m=n gives the actual quotient identity
on residue classes, rather than an arbitrary ring automorphism; no flatness of B/A
is assumed, including m<n. For empty Y the only ordinary and pro-etale objects are
zero and the single map is invertible; the existential and uniqueness clauses remain
valid. The argument does not use r>0, so r=0 is included. The coordinate index is
`ULift (Fin r)`, retaining all finite dimensions at scheme universe u; coefficients
are `ULift.{u+1,u}` into the established module-value universe, while the small sites
keep object universe u+1 and morphism universe u. None are equated to force an API.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "Descent of finite coefficient closed exceptional counit mate from proetale to etale derived categories"`:
  eight hits, on condensed counits, derived adjunction counits and the etale forgetful
  fully faithful functor; none is this coefficient descent theorem.
- `msearch.py ... loogle "CategoryTheory.Adjunction.homEquiv, CategoryTheory.Functor.FullyFaithful"`:
  one hit, `Adjunction.restrictFullyFaithful_homEquiv_apply`; it is a general restricted
  adjunction identity, not the required geometric assertion.
- `msearch.py ... grep 'FullyFaithful.*(IsIso|preimage)|isIso.*FullyFaithful|counit.*descen' CategoryTheory`:
  25 general full-faithfulness and preimage-isomorphism hits, none with these geometric maps.
- `rg` of both live Lean roots for `closedDescent`, `ClosedDescent`, `closedDualizing`,
  `ClosedDualizing`, `dualizingClosed`, `DualizingClosed`, the exact blueprint tag and
  coefficient/closed combinations: no matching item declaration. Existing finite closed
  shriek, site counit transport, finite dualizing assembly, and finite-duality comparisons
  were opened; they respectively give the pro-etale input theorem, a one-ring normalization,
  the downstream structure-morphism result, and duality/site comparisons, rather than this
  two-ring descent with its coefficient square. The downstream parent is deliberately not
  imported. `grep -rn` of the exact item tag in `lean/WeilConjectures` returned no match.
- Both proposed public declaration names were searched in `lean/Sheaf` and
  `lean/WeilConjectures`: no collision.

Validation: the prescribed `scompile.py` compiled this module in module mode against the
live published build, both as a sandbox file and under its library module name, with no
errors or warnings. No global build, local Lake invocation, or shared-source edit was made.


## New nodes

`def-sf-etale-proetale-ambient-direct-image-comparison` owns the existing
`AlgebraicGeometry.ProEtale.directImageComparisonAmbientPullbackIso` and
`AlgebraicGeometry.ProEtale.directImageComparisonAmbient` in
`Sheaf.Paper.EtaleProEtaleScalarMate`, with `existing: true` and no delivered module.
Its source is the exact inverse-image square and canonical transformation in the
current blueprint's `sk-thm-pe-direct-image-comparison/_section.md`, with the
published geometric counit-mate normalization. Its first clause is exactly the
five-isomorphism composite defining the pullback square (lines 139–152); its second
is exactly `mateEquiv` under the two `derivedUpperStarLowerStarAdjunction`s
(lines 158–166). The component transpose therefore uses the actual etale counit.
The ring binder is `A : Type (u + 1)` with `[CommRing A]`, the schemes have universe u,
and f is arbitrary. The statement makes no isomorphism claim for the direct-image
mate; no boundedness or geometric finiteness is needed to define it.

Searches: LeanSearch of the canonical etale/pro-etale direct-image mate returned
8 general adjunction/mate hits; Loogle `CategoryTheory.mateEquiv` returned 12 general
mate identities; Mathlib grep in CategoryTheory/Adjunction returned 5 occurrences
of the general mate. The new node records their actual queries and results.
DAG grep and blueprint-reference searches found no definition node owning the exact
ambient L-pullback comparison. Existing scalar-mate, scalar-counit-transposes and
scalar-pullback-cube theorem records mention these helpers, but their statements
assert compatibilities. Source grep finds the exact two definitions in the published
module, so the node reuses them with no duplicate definition. The bounded-below
comparison and termwise unbounded comparison have different Lean presentations;
the integral ambient encoding concerns coefficient-model comparison squares.

## Return repair

The independent review returned immutable head `25ffe2b79f89` for H2: the newly
added theorem statement dependency was only used for its plain definitions.
Replaced the added `lem-sfb-etale-proetale-scalar-mate` statement edge by
`def-sf-etale-proetale-ambient-direct-image-comparison`. The scalar-mate theorem
remains an inherited proof dependency for proof step 2. The same public import
supplies both the existing comparison definitions and that proof prerequisite.
No inherited stage-1 statement or proof edge was edited. Comparing with current
main, the item's changes are still only `lean` and the three extra statement edges;
its accepted split is preserved. The Lean module is retained unchanged from the
returned packet, whose clause-by-clause mathematics the reviewer accepted.

## Second reading by NH

Repair self-check, with the saved module, live node and published comparison module
open: deltaA/deltaB are literally `.app N` and `.app NB` of the newly owned
`directImageComparisonAmbient`; the new node's d is its literal pullback-isomorphism
argument. No scalar-mate theorem conclusion appears in the statement. Every geometric,
positive quotient-level, dualizing-input, counit uniqueness, isomorphism, normalized
square, site-image and independent D+ endpoint clause remains the one tabulated
above and accepted in the independent review. The empty scheme, m=n, r=0 and arbitrary
commutative coefficient cases of the added definition have no new excluded cases.
This is a worker self-check; the independent maintainer review reads the delivery.
