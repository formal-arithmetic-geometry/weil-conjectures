## Worker report

The module `Sheaf.AlgebraicGeometry.NilpotentCoefficientDirectImageBound` states
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_nilpotent_quotient_bound`.
Its only theorem has proof `sorry`. It introduces no definitions, helper axioms,
new nodes, dependency modules, or statement corrections. The node is otherwise unchanged.

The source read was `literature/stacks-project/derived.tex`,
`lemma-higher-derived-functors`, lines 7047–7093 (Tag 015B): part (1) gives the
long exact sequence, part (2) includes degree zero. This is the agent-written
nilpotent-coefficient application recorded in the node, rather than a claim that
Stacks or Bhatt–Scholze states this exact general theorem. The docstring gives
all five DAG proof steps, including sheaf gluing, the canonical quotient action,
coefficient restriction, exactness, and the finite induction preserving the degree.

Every hypothesis and clause is rendered as follows:

| Node | Lean |
| --- | --- |
| Schemes X and Y and morphism f:X→Y | `{X Y : Scheme.{u}} (f : X ⟶ Y)` |
| Quasi-compact, quasi-separated f | `[QuasiCompact f] [QuasiSeparated f]` |
| Commutative coefficient ring R | `(R : Type (u + 1)) [CommRing R]` |
| Ideal I of R | `(I : Ideal R)` |
| Integer exponent t≥1 | `(t : ℕ) (ht : 1 ≤ t)`; positive integers are exactly these naturals |
| I^t=0 as an ideal | `(hI : I ^ t = ⊥)` |
| Every integer bound N, including negative N | `(N : ℤ)` |
| All quotient-coefficient module sheaves Q | `∀ (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (R ⧸ I)))` in `hN` |
| Every integer q≥0 above N | `(q : ℤ), 0 ≤ q → N < q →` in both premise and conclusion |
| Vanishing of the quotient-coefficient higher direct image | `IsZero (higherDirectImage (R ⧸ I) f q Q)` |
| Every R-module sheaf M | `∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))` |
| Vanishing over R | `IsZero (higherDirectImage R f q M)` |
| The same N works independently of t | The conclusion uses exactly the input N, with t universally quantified |
| No finiteness or flatness of M | M is an unrestricted object of this sheaf category |

The coefficient and module universe is the standard `u+1` convention of the
existing six-functor and constructible-sheaf interface, also used by the
coefficient-change proof dependency. It includes small rings by cumulativity.
`R ⧸ I` is Mathlib's actual ideal quotient ring in the same coefficient universe.
The fixed-coefficient encoding `Sheaf ... (ModuleCat R)` is explicitly authorized
by `def-weil-pbc-etale-sheaves` (its recorded note gives both coexisting encodings).
No ringed-site module category or derived-image construction is copied here.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom` (source lines 36–46 and 72–74).
- `def-weil-scheme-morphism-properties` is explicitly a convention with no declaration.
  Its quasi-compact notion is Mathlib's `AlgebraicGeometry.QuasiCompact`
  (Morphisms/QuasiCompact.lean, lines 38–45); quasi-separatedness is
  `AlgebraicGeometry.QuasiSeparated` (Morphisms/QuasiSeparated.lean, lines 48–52),
  the quasi-compactness of the diagonal. No stronger separation condition occurs.
- `def-weil-pbc-etale-sheaves`: public import
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves`; the category used is its
  recorded `CategoryTheory.Sheaf`, with coefficients `ModuleCat.{u + 1} R`,
  following the node's fixed-coefficient convention. No locally constant,
  constructible, finite, or torsion condition is imposed.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (base-change precomposition)
  and `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`, now located in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
  `AlgebraicGeometry.Etale.higherDirectImage` from the public import
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` is exactly
  degree-q homology of this bounded-below derived image of a sheaf in degree zero.
  Read its complete signature and body at lines 101–110. The record's derived
  declaration is in a newer source module, already imported transitively;
  no interface repair is needed.

Every recorded proof dependency has its module imported without `public`:

- `def-weil-pbc-constant-sheaf`: Mathlib.CategoryTheory.Sites.ConstantSheaf,
  `CategoryTheory.constantSheaf` (sheafification of the constant presheaf).
- `def-weil-pbc-sheafification`: Mathlib.CategoryTheory.Sites.Sheafification,
  `CategoryTheory.presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`.
- `def-weil-sheaf-of-modules-category`: Sheaf.CategoryTheory.RingedSiteModules,
  `CategoryTheory.ringedSiteModules`, a transparent abbreviation of `SheafOfModules`.
- `lem-sbc-coefficient-higher-direct-image-zero`:
  WeilConjectures.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero,
  `AlgebraicGeometry.Etale.isZero_higherDirectImage_restrictScalars_iff`.
  Its full signature covers arbitrary commutative coefficient rings, every
  integer degree, and precisely the given qcqs morphism.
- `lem-weil-pbc-derived-functor-long-exact`:
  WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence,
  `CategoryTheory.ShortComplex.ShortExact.exists_rightDerived_full_long_exact`.
- `lem-weil-pbc-module-direct-image-left-exact`:
  Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact,
  `AlgebraicGeometry.Etale.existsUnique_constantModuleDirectImage_leftExact`.
- `lem-weil-pbc-module-sheaves-enough-injectives`:
  Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives,
  `AlgebraicGeometry.Scheme.etaleModule_enoughInjectives`.

Edge cases checked before writing:

- t=1 forces I=0, so this is invariance under R/0 and the filtration has one piece.
- t=0 is excluded by the stated hypothesis; no case required by the node is lost.
- For R=k[ε]/ε² and I=(ε), the two annihilator pieces illustrate that no flatness
  of R/I or M is available or needed. The proof uses the annihilator filtration,
  rather than assuming the I-adic filtration quotients preserve injectives.
- N<0 includes q=0 on both sides; the initial part of the long exact sequence is
  explicitly retained. For a nonempty scheme and identity f, this hypothesis
  does not hold for nonzero quotient sheaves, as expected.
- For q=N or negative q, neither side claims additional vanishing.
- M=0, the zero ring, I=⊥, and empty X or Y introduce no nontriviality or
  nonemptiness assumptions. For the zero ring even I=⊤ is nilpotent and all
  module sheaves are zero. All are allowed by the signature.
- There is no Noetherian, finite generation, finite presentation, or flatness
  assumption on the ring, the ideal, or the sheaves.

Searches actually performed (via `msearch.py NE
lem-sf-nilpotent-coefficient-direct-image-bound`):

- LeanFinder: “A nilpotent ideal I in a coefficient ring R preserves a uniform
  vanishing bound N for higher direct images of every etale module sheaf along
  a quasi compact quasi separated scheme morphism”. Eight hits concern qcqs
  sections, nilpotence on covers, and formal étaleness; none states this theorem.
- Loogle: `CategoryTheory.Functor.rightDerived, Ideal.Quotient` returned zero hits
  with “unknown identifier Ideal.Quotient”; recorded as an invalid query, not
  evidence of absence. Repeated with
  `CategoryTheory.Functor.rightDerived, IsNilpotent`: zero hits, valid query.
- Mathlib grep: `nilpotent.*(cohomolog|derived)|cohomolog.*nilpotent` returned five
  hits from Algebra/Lie/CartanCriterion.lean; unrelated to sheaf direct images.
- `rg` on both lean/WeilConjectures and lean/Sheaf for higherDirectImage and
  nilpotent/direct-image combinations found the existing coefficient-change
  theorem and other direct-image interfaces, but no matching nilpotent bound.
  A narrower case-insensitive scan found the derived tensor reduction bound,
  which concerns complexes of ordinary modules, not this theorem.
- `grep -rn` for this node id in lean/WeilConjectures returned no hits.
- `rg` for the proposed declaration and NilpotentCoefficientDirectImageBound in
  dag/lean_names_upstream.json and both source trees returned no matching
  declaration or module. An unrelated NilpotentCoefficientAdjustment import
  concerns power-series coefficient rings.

No statement fault or disputed mathematical assertion was found.

Validation: `scompile.py` compiled both the sandbox probe and the actual library
module cleanly on the server (18.6 s and 17.8 s), with no errors or warnings.
The entire module has maximum line length 92. Every variable and universe is
explicitly bound. The only postponed theorem is the item itself.

Delivery validation: `deliver2.py NE lem-sf-nilpotent-coefficient-direct-image-bound
--no-push` returned OK: the packet passes the server preflight and compiles.
A source comparison confirms that only the node field `lean` changes and its
recorded signature is verbatim from the module.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
