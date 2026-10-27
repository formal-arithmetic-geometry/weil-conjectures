## Worker report

Item: `lem-sfb-positive-weight-luna-coordinates`.
Module: `Sheaf.AlgebraicGeometry.PositiveWeightLunaCoordinates`.
Main declaration: `AlgebraicGeometry.positive_weight_luna_coordinates`.

The statement is unchanged. The theorem has exactly one `sorry`. Six explicit auxiliary
constructions give the evaluation at the supplied point, the scalar coordinate of an
F-point of G_m, restriction of the actual action, its actual pullback, the evaluation
kernel, and the morphism defined by the supplied coordinates. They implement the objects
introduced in this item, and do not introduce independent notions or arbitrary maps.
Their declarations are listed in `lean.declarations` and their docstrings carry the item ID.
There are no new nodes, dependency repairs, hollow definitions, or statement corrections.

Source read: Milne, Algebraic Groups (2017), printed pp.267--270, Lemmas 13.35--13.36,
Example 13.37, and Theorem 13.41 with its proof. The node's globally smooth case makes
integrality follow from connectedness and regularity. The latest blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
was also read; this item is the inherited algebraic-group supporting input recorded in
its DAG ancestry, not the blueprint unit's own statement.

### Hypothesis and conclusion correspondence

- Algebraically closed field F: section parameters `(F : Type u) [Field F]`, and theorem
  parameter `[IsAlgClosed F]`. There is no characteristic assumption.
- Affine F-scheme Z: `(Z : Over (Spec (.of F)))` and `[IsAffine Z.left]`. This is a general
  affine scheme over F, not just a chosen spectrum presentation.
- Finite type: `[LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]`, exactly the recorded
  finite-type dependency's conjunction.
- Smooth and connected: `[Smooth Z.hom] [ConnectedSpace Z.left]`. The latter includes
  nonemptiness as in the node. The point below also witnesses nonemptiness.
- A scheme G_m-action: `μ : StandardGroupSchemes.multiplicative F ⊗ Z ⟶ Z` is a morphism
  in the category of F-schemes; its tensor product is their fibre product. `hunit` says
  μ(1,u)=u using the canonical group identity and the left unitor. `hassoc` says
  μ(st,u)=μ(s,μ(t,u)), using the canonical group multiplication and associator. Thus μ
  is a regular action, not merely an abstract action of F-points.
- Rational point z: `z : 𝟙_ (Over (Spec (.of F))) ⟶ Z`; the tensor unit is Spec F with
  its identity structure map.
- Fixedness: `hfixed` is an equality of F-scheme morphisms G_m × Spec F → Z,
  `(id ⊗ z) ≫ μ = snd ≫ z`. Fixedness is scheme-theoretic, not an assumed pointwise
  substitute for the action law.
- A = Γ(Z,O_Z): `((algΓ (.of F)).obj Z).unop` is Mathlib's actual relative global
  coordinate algebra. Its underlying commutative ring is Γ(Z.left,⊤), with its canonical
  F-algebra structure.
- Evaluation A→F: `lunaPointEvaluation F Z z` is `z.left.appTop`, followed by the
  canonical `Scheme.ΓSpecIso` identification of Γ(Spec F) with F. Its kernel is exactly
  `lunaMaximalIdeal F Z z`, the node's m.
- The ideal m² and quotient m/m²: `(lunaMaximalIdeal F Z z).Cotangent` is Mathlib's
  `Ideal.Cotangent`. Its `Ideal.toCotangent` quotient map kills exactly the elements
  of m², by `Ideal.toCotangent_eq_zero`. No alternative quotient is defined.
- Tangent space: `Module.Dual F (lunaMaximalIdeal F Z z).Cotangent` is exactly
  Hom_F(m/m²,F).
- Direct sum of positive character subspaces, empty sum allowed: `hpositive` asserts
  existence of a basis `b : Module.Basis (Fin r) F (Module.Dual F m.Cotangent)` and
  integer weights `w`, with `∀ i, 0 < w i`. The following equation is precisely the
  eigenvector equation for the differentiated action. For each torus point t and each
  x,y∈m with y=μ_t^*x it says `b i ([y]) = t^(w i) * b i ([x])`.
  The differentiated point action on a tangent functional is precomposition by the
  cotangent pullback, so this is `dμ_t(b i)=t^(w i)b i`, with the sign in the node.
  The redundant representative y introduces no hypothesis: scheme-theoretic fixedness
  implies μ_t^*(m)⊆m, so for every x this y exists and is unique. Quantifying over all
  representatives avoids manufacturing a second cotangent map or hiding a choice.
  Since the tangent space is finite-dimensional (already from finite type, or from
  `hbasis`), existence of this finite eigenbasis is equivalent to the node's direct sum
  decomposition. Algebraically closed F is infinite; rational points of G_m detect
  characters, so using all rational t gives the actual character weights in every
  characteristic. Repeated weights are permitted and `r=0` is permitted.
- The scalar t in the weight formulas: `lunaPointScalar F t` evaluates the actual Laurent
  coordinate `T 1` at the F-point t of the canonical G_m. These points are exactly Fˣ,
  so its value is nonzero. Integer powers use F's `zpow`, including negative exponents;
  no positivity of the supplied n is silently assumed.
- Supplied `a_1,...,a_d ∈ m`: `(d : ℕ) (a : Fin d → lunaMaximalIdeal F Z z)`.
- Their classes form an F-basis: `hbasis` asserts a `Module.Basis (Fin d) F m.Cotangent`
  whose i-th vector is exactly `m.toCotangent (a i)`. It says both independence and
  spanning, without replacing the supplied lifts.
- Homogeneity with specified integer n_i: `(n : Fin d → ℤ)` and `hhomogeneous` assert
  `lunaActionPullback F Z μ t (a i) = lunaPointScalar F t ^ n i • (a i)` for every t,i.
  This is exactly the regular-function equality `a_i(tu)=t^(n_i)a_i(u)`. Pullback is
  computed by the actual action morphism via `algΓ.map`. Equality of these global
  functions states the equation for all u; no point-evaluation approximation is used.
- Stipulated λ: `lunaCoordinateMap` applies the standard `algΓAlgSpecAdjunction.homEquiv`
  to the opposite of `CommAlgCat.ofHom (MvPolynomial.aeval a)`. Its target is exactly
  `StandardGroupSchemes.affine F (MvPolynomial (Fin d) F)`, i.e. Spec F[T_1,...,T_d].
  The coordinate algebra map sends T_i to exactly the supplied a_i.
- Conclusion: `IsIso (lunaCoordinateMap F Z d (fun i ↦ (a i : ...)))` is an isomorphism
  in `Over (Spec F)`, hence explicitly an isomorphism of F-schemes of this actual map.
  This includes d=0: the empty-variable polynomial ring is canonically F, giving the
  node's identification Z≅Spec F. This is the same conclusion specialized, not a
  second independent existence assertion requiring another theorem.

### Dependency declarations used

All nine statement-dependency node records and their full relevant source signatures
and docstrings were read. The recorded declarations are used, with no repairs:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: the record explicitly identifies the algebraically closed
  predicate as `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic; the theorem uses that
  predicate on F rather than requiring F to be a chosen `AlgebraicClosure K`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and its morphisms,
  Mathlib.AlgebraicGeometry.Scheme. The standard relative encoding is `CategoryTheory.Over`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact.
- `def-sc-gm-ga`: `StandardGroupSchemes.multiplicative`, `.multiplicativeGroup`, and
  `.affine`, Sheaf.AlgebraicGeometry.StandardGroupSchemes. The canonical group instance
  supplies `MonObj.one` and `MonObj.mul`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-connected-scheme`: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`, and the canonical
  Gamma-Spec constructions, Mathlib.AlgebraicGeometry.Scheme and .Group.Affine.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` and `MvPolynomial.aeval`,
  Mathlib.Algebra.MvPolynomial.Basic and .Eval.

Additional existing standard constructions used directly: `algΓ`, `algΓAlgSpecAdjunction`
(Mathlib.AlgebraicGeometry.Group.Affine); `Ideal.Cotangent`, `Ideal.toCotangent`
(Mathlib.RingTheory.Ideal.Cotangent); `Module.Dual` (Mathlib.LinearAlgebra.Dual.Defs);
`Module.Basis`; and the Cartesian monoidal structural maps. These are not redefined.

The module imports the already stated proof dependencies with plain imports:
WeilConjectures.AlgebraicGeometry.Regular (both `IsRegular.of_smooth` and
`IsRegular.isIntegral`), Sheaf.RingTheory.KrullIntersectionLocalization, and the recorded
Mathlib files for finite-type affine rings, Noetherian spectra, integral schemes,
affine stalk localization/function fields, and affine fibre products. Statement dependency
modules are public imports (some are also exposed transitively through the canonical group
module). `lem-sfb-positive-graded-regular-polynomial` has no Lean record or Mathlib match
in the read repository; it is only a proof dependency, not needed to state this item, so
there is no module to import. Its use is fully documented in the theorem's step-7 proof
paragraph. No missing statement prerequisite was encountered.

### Edge cases and checks

- d=0: `Fin 0` and the empty coordinate family elaborate normally. `hbasis` asserts that
  m/m² is zero and the same map has the required zero-variable polynomial target.
- Zero tangent space: `r=0` is allowed in `hpositive`; no `Nonempty (Fin r)` occurs.
- Positive characteristic, including 2: no `CharZero`, `NeZero (p : F)`, division by an
  integer, separability, or characteristic-dependent hypothesis occurs.
- Negative and zero supplied integer n_i remain expressible. The hypothesis of positive
  tangent weights forces them positive when coordinates are nonzero in the basis;
  the theorem does not assume that consequence independently.
- Repeated positive weights are allowed, so nonlinear homogeneous lifts such as
  `(x,y+x²)` with weights `(1,2)` are covered. Nonhomogeneous lifts are not admitted.
- A trivial action on positive-dimensional Z cannot satisfy `hpositive`, because it
  would make a nonzero tangent vector have every positive character. Thus positivity
  is not vacuous. The point scheme with its zero tangent space is admitted.
- Disconnected and nonsmooth schemes are excluded exactly by the node's stated
  hypotheses; the empty scheme is excluded both by connectedness and the supplied point.
- `u` is explicitly bound; F and the arbitrary scheme Z share the standard scheme
  universe. All variables are explicitly bound, and `set_option autoImplicit false`
  enforces this. There is no file-local notation, instance, abbreviation, or private data.
- The entire final file compiles under module mode, both as the wrapper's sandbox
  and library module, cleanly in about 2 seconds each using scompile.py. The only
  postponed declaration is the main theorem; every definition has actual data.
- Every Lean line is at most 100 characters. The node copy changes only `lean`.

### Searches

The prescribed msearch queries were run with group Q130 and this item:

1. LeanFinder: "Homogeneous coordinates at a fixed point with positive tangent weights
   on a smooth connected affine scheme give an isomorphism with affine space". Eight
   results, all standard affine-space coordinate/Spec isomorphism formulas, including
   `AffineSpace.SpecIso`, `AffineSpace.isoOfIsAffine`, their coordinate formulas and
   `AffineSpace.toSpecMvPolyIntEquiv_apply`. Read these interfaces; none states the
   positive-weight global-coordinate theorem.
2. Loogle: `"LaurentPolynomial", "eval"`. Twelve results: `LaurentPolynomial.eval₂`,
   `.smeval`, `.leval` and their evaluation formulas. They describe scalar evaluation,
   not the desired theorem. The supplied point's scalar was instead constructed
   directly from canonical global-section evaluation, requiring no auxiliary proof.
3. grep (msearch): `Luna|strictly.?definite|positive.{0,40}tangent|tangent.{0,40}positive`.
   Seven hits, all unrelated analysis tangent-cone material in Calculus/LocalExtr/Basic
   and TangentCone/{Defs,Real}. No algebraic-geometric match.
4. LeanSearch: "Every homogeneous cotangent basis at a fixed point with positive tangent
   weights on a smooth connected affine scheme defines an isomorphism with affine space".
   Eight results: `AffineSpace.isoOfIsAffine`, `.isoOfIsAffine_hom`, `.homOverEquiv`,
   `.isoOfIsAffine_hom_appTop`, `AffineBasis.ext`, and submersive-presentation cotangent
   constructions. Their signatures were inspected; none asserts this theorem.
5. Source grep/rg on `lean/WeilConjectures`, `lean/Sheaf` and
   `dag/lean_names_upstream.json`: `Luna|luna|positiveWeight|PositiveWeight|gmAction|GmAction`
   and the proposed declaration names. No existing Luna theorem or conflicting name.
   `grep -rn 'lem-sfb-positive-weight-luna-coordinates' lean/WeilConjectures` gave no hit.
6. Focused source searches for `CotangentSpace|cotangentSpace`, `Ideal.Cotangent`,
   `mapCotangent`, `PointDerivation`, `appTopAlgHom`, `algΓ`, `ΓAlgebra`, and affine-space
   coordinate maps located the actual Mathlib quotient and adjunction interfaces used
   here. The StandardGroupSchemes source was read through its canonical G_m construction.

The requested CompactObject example module on the current shared checkout is withdrawn
and contains no declarations; its node points to the existing upstream notion. I followed
the current module-mode/import/docstring conventions and the non-withdrawn canonical
StandardGroupSchemes module. This does not require a node repair for the present item.

No STATEMENT-DISPUTED issue was found.

## Second reading by Q130

This is an explicit self-audit, not an independent second worker's review: the dispatcher
brief forbids starting other agents and assigns the independent reading to the maintainer.
I reopened the final Lean file and node and checked each clause using the correspondence
above. In particular I rechecked the order of the two G_m factors in associativity,
fixedness as a morphism equality, the sign of precomposition on tangent functionals,
the totality of the quantified cotangent-representative equation, and that the conclusion
uses the exact supplied a_i through aeval. The kernel and quotient are the actual m and
m/m², and both empty bases are admitted. No mathematical mismatch was found; the draft
was extended with the full eight-step proof docstring and the available proof imports.
