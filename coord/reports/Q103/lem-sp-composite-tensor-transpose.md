## Worker report

The module `Sheaf.CategoryTheory.SmoothPurityCompositeTensorTranspose` states
`CategoryTheory.spCompositeTensorTranspose_eq`, with its entire proof `sorry`.
Its six helpers construct the maps appearing in the node with actual data:
`spTensorCounit` is q, `spTensorCounitMate` is t,
`spCompositeCoefficientIso` is mu, `spCompositeTensorDirect` is the first arrow,
`spCompositeTensorIterated` is the second arrow, and
`spCompositeTensorTranspose` is their specified common inverse Hom transpose.
No node statement or dependencies have been changed. No new definition node or
replacement dependency module is needed: the helpers spell out formulas belonging
to this statement, rather than introducing independent mathematical notions.

Source read: the current blueprint at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/`
`sk-prop-sp-composition-factors.proof.md`, paragraph (2), together with the node's
eight-step categorical expansion. The source compares projection formulas and
counits under the composite adjunction. Its final sentence also explicitly uses
naturality of the tensor map for f. The node states this abstract calculation,
including unit normalization; the supplied docstring reproduces all eight steps.

Hypothesis-by-hypothesis correspondence:

- The categories C_X, C_Y, C_Z are `X`, `Y`, `Z`, each with `Category`,
  `MonoidalCategory`, `SymmetricCategory`. Their six object and morphism universes
  `uX vX uY vY uZ vZ` are independent and explicitly declared.
- The symmetric strong monoidal pullbacks are `Pf : Y ⥤ X`, `Pg : Z ⥤ Y`,
  with `[Pf.Braided]`, `[Pg.Braided]`. `Functor.Braided` extends both
  `Functor.Monoidal` and `Functor.LaxBraided`; its braiding equation says exactly
  that the tensorator identifies the image of symmetry with symmetry of images.
- The instruction to identify P_h = P_f P_g as symmetric monoidal functors is
  implemented by using `Pg ⋙ Pf` everywhere for P_h, with its composite structure.
  This is identification of the specified structures, rather than an extra
  equality only of underlying functors.
- `Ff`, `Fg`, `Fh`, `Gf`, `Gg`, `Gh` have the directions forced by the node.
  `af : Ff ⊣ Gf`, `ag : Fg ⊣ Gg`, `ah : Fh ⊣ Gh` supply their specified
  natural Hom bijections, units and counits. The section variables are explicitly
  typed, and Lean binds the used variables in each declaration; autoImplicit is false.
- `α : Ff ⋙ Fg ≅ Fh` and `c : Gh ≅ Gg ⋙ Gf` are the stated natural isomorphisms.
  `hc` is exactly F_g F_f(c_K) followed by the composite counit, equal to alpha at
  G_h K followed by epsilon_h. `af.comp ag` has counit
  `Fg.map (af.counit.app (Gg.obj K)) ≫ ag.counit.app K`, so no counit is altered.
- `πf`, `πg`, `πh` have type F_u M tensor L isomorphic to F_u(M tensor P_u L),
  with the node's direction. Isomorphisms provide actual inverses, not merely
  existence of unspecified comparisons.
- `hf_natural`, `hg_natural`, `hh_natural` express joint naturality in both M and L.
  Joint naturality is equivalent to the two separate naturality equations by
  taking either morphism to be the identity and composing the resulting equations.
- `hf_unit`, `hg_unit`, `hh_unit` express projection unitality: apply pi at 1,
  then F of the inverse unit tensorator in its second tensor factor and the right
  unitor, to recover the right unitor of F M. `OplaxMonoidal.η` is the inverse
  of `Monoidal.εIso`, not a hypothetical equality P(1) = 1.
- `hf_assoc`, `hg_assoc`, `hh_assoc` are projection associativity: one route
  uses the target associator, pi at L tensor L', and F of the inverse tensorator
  and inverse source associator. The other uses pi at (M,L) tensored with 1,
  followed by pi at (M tensor P L,L'). This is the ordinary right tensor action
  associativity, written without suppressing the tensorator or associators.
- `hπ` says `(α_M tensor 1) ≫ πh` equals `πg ≫ Fg(πf) ≫ α`, exactly the displayed
  compatibility in the node, with Lean's first-then composition convention.
- Omega_f, Omega_g, Omega_h are the expressions `Gf.obj (𝟙_ Y)`,
  `Gg.obj (𝟙_ Z)`, `Gh.obj (𝟙_ Z)`. W is expanded as
  `Pf.obj (Gg.obj (𝟙_ Z)) ⊗ Gf.obj (𝟙_ Y)`.
- The sole extra invertibility hypothesis is
  `IsIso (spTensorCounitMate Pf Ff Gf af πf (Gg.obj (𝟙_ Z)))`, exactly rho.
  `spCompositeCoefficientIso` composes `c.app 1` with `(asIso rho).symm`,
  so its forward map is mu = rho inverse after c_1 and its inverse is the
  required map W to Omega_h.

Clause-by-clause correspondence:

- `spTensorCounit` is F of symmetry, inverse pi, epsilon at the coefficient unit
  tensored with identity, and the left unitor, precisely q_{u,L}.
  `spTensorCounitMate` uses `adj.homEquiv` of that exact q to define t_{u,L}.
- `spCompositeTensorDirect` is `1 tensor mu.inv`, then t_h,K, then `c.hom.app K`.
- `spCompositeTensorIterated` first takes the inverse associator from
  P_f P_g K tensor (P_f Omega_g tensor Omega_f) to the left association,
  then the forward tensorator of P_f, then `Pf.map t_g,K tensor 1`, then t_f,GgK.
  These first two factors are exactly the node's canonical reassociation.
- `spCompositeTensorTranspose` starts with F_g F_f of symmetry at P_h K and W,
  then `Fg.map (πf W (Pg.obj K)).inv`, then `(πg (Ff.obj W) K).inv`.
  These are the inverse of the specified composite projection, in the correct
  inverse order. It ends with
  `(Fg.map (q_f,Omega_g) ≫ ag.counit.app 1) tensor 1`, then the left unitor.
  The parenthesized expression is exactly s in the node.
- The first conjunct quantifies over every K, and asserts that the inverse
  composite Hom bijection of each of the two arrows equals that common transpose,
  and asserts equality of the arrows as its third clause.
- The remaining six conjuncts give, for f, g, h in turn, equality of t at 1
  with `(inverse unit tensorator tensor 1) ≫ left unitor`, and naturality for
  every morphism `l : L ⟶ L'`. They include noninvertible morphisms.
- No geometric, orientation, derived evaluation or coefficient-finiteness
  assumptions occur. There is no restriction on K or arbitrary coefficients L,
  and no inversion of t_f,L outside the explicitly assumed rho.

Recorded dependency interfaces read and used:

- `def-sfb-monoidal-category`: `Mathlib.CategoryTheory.Monoidal.Category`,
  `CategoryTheory.MonoidalCategory`, lines 87-108 and 162-210, including
  tensor bifunctor, naturality, pentagon and triangle.
- `def-sfb-strong-monoidal-functor`: `Mathlib.CategoryTheory.Monoidal.Functor`,
  `Functor.CoreMonoidal`, lines 620-651. The equivalent class presentation used
  here is `Functor.Monoidal`, lines 389-414, with specified inverse tensorators.
- `def-weil-pbc-adjunction-mate`: `Mathlib.CategoryTheory.Adjunction.Mates`,
  `CategoryTheory.mateEquiv`, lines 70-113. Its underlying adjunction notions are
  `Adjunction`, `homEquiv`, `counit` in `Adjunction.Basic`, lines 108-182.
- Proof dependencies `lem-weil-pbc-adjunction-of-natural-bijection` and
  `lem-sfb-adjunction-transpose-square`: `Adjunction.mkOfHomEquiv`,
  `homEquiv_counit`, `homEquiv_naturality_right_square_iff` in
  `Mathlib.CategoryTheory.Adjunction.Basic`, lines 270-276, 351-365, 436-455.
  This module is transitively available through the public Mates import.
- Symmetry and its functorial preservation use Mathlib's existing
  `SymmetricCategory`, `Functor.Braided`, `Functor.LaxBraided` from
  `Monoidal.Braided.Basic`, lines 368-374, 386-389, 532-539.

Searches actually performed:

- msearch LeanFinder: "Tensor maps from projection formula and adjunction counit
  have equal transposes for composite adjunctions": eight hits, including
  `Adjunction.map_μ_comp_counit_app_tensor`, `MonoidalClosed.compTranspose`,
  Frobenius morphisms, and tensor/unit formulas. None has this statement's
  specified projections, comparison isomorphisms and three concluding clauses.
- msearch Loogle: "CategoryTheory.Functor.ProjectionFormula,
  CategoryTheory.Adjunction.homEquiv": zero hits, unknown upstream identifier
  `CategoryTheory.Functor.ProjectionFormula`. This is not a Mathlib declaration.
- msearch grep: "ProjectionFormula|tensorCounitTranspose", CategoryTheory:
  zero Mathlib hits.
- msearch LeanSearch: "projection formula adjunction tensor counit composite
  transpose": eight hits including `Adjunction.comp_counit_app` and counit
  formulas, but no exact match.
- msearch Loogle: "CategoryTheory.Adjunction.homEquiv": twelve hits, supplying
  the hom bijection, counit formula, and composition bijection used here.
- Direct rg searches in `lean/WeilConjectures` and `lean/Sheaf` for composite
  tensor transposes, projection associativity and projection formulas, plus
  node-id searches in `lean/WeilConjectures` and `dag/lean_names_upstream.json`.
  The latter have no attachment for this node.
- Read `WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap`:
  `projectionTensorMap` is the related two-parameter map with input
  G M tensor P N and target G(M tensor N); it is not q or t as oriented here.
  Its composition theorem lacks the stated common transpose and unit clauses.
- Read `Sheaf.CategoryTheory.CompositeTensorTranspose`: the older
  `SecSmoothPurity.composite_tensor_transpose` belongs to
  `lem-pur-composite-tensor-transpose`, uses the left-coefficient
  `Functor.ProjectionFormula`, and has only the two canonical adjunctions.
  It does not state the theorem with the arbitrary specified h adjunction,
  alpha and c, rho invertibility, or all the unit/naturality conclusions.
  This module is therefore not an exact existing-declaration attachment.
  The present module uses neither a second projection-formula structure nor
  any private copy of the dependency definitions.

Edge cases checked before writing: coefficient L = 1 requires inverse unit
comparison and the unitor, which are kept explicitly; K = 1 is included.
No zero, additive or nonempty hypothesis is added. Monoidal categories already
have their specified unit object; terminal/trivial examples are not excluded.
Identity functors and adjunctions normalize all helpers to the usual unit and
symmetry identifications. Noninvertible l is permitted in the naturality clauses.
Only rho is inverted, so noninvertible general tensor maps remain allowed.
Separate object and morphism universes are retained for all three categories.
There is no index type, characteristic, scheme, or coefficient restriction.
No `STATEMENT-DISPUTED` issue was found, and no source correction was needed.

Validation: the prescribed scompile.py compiled this single module both as a
sandbox module and at its library module name, with exit code 0 and no warnings
or errors (53.4 seconds and 1.3 seconds respectively, within the 60-second limit).

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
