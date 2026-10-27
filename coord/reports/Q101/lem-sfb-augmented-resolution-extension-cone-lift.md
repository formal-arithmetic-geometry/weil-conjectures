## Worker report

The module `Sheaf.Algebra.Homology.AugmentedResolutionExtensionConeLift` states
`CochainComplex.augmentedResolution_extension_cone_lift`. It has one named theorem,
whose whole proof is `sorry`, and introduces no definitions. The node is unchanged
except for `lean`. No missing dependency interface, new node, statement correction,
or mathematical dispute was found.

Hypothesis and clause correspondence:

- The abelian category E is `C : Type u`, `[Category.{v} C]`, `[Abelian C]`.
  `[HasDerivedCategory.{w} C]` fixes the localization morphism universe, independently
  of the object and original morphism universes, as in def-weil-size-convention.
- The objects N, E, X and maps i, p are respectively `S.X₁`, `S.X₂`, `S.X₃`,
  `S.f`, `S.g` for `S : ShortComplex C`. The zero composite is included in S;
  `hS : S.ShortExact` supplies exactness, monicity and epicity. Bundling adds no
  condition and omits none.
- `P : CochainComplex C ℤ` is the given cochain complex. `hP` says its objects
  are zero for every strictly positive integer degree. Categorical `IsZero` is
  the invariant meaning of zero object, without requiring a particular chosen zero.
  The first two differentials are `P.d (-1) 0` and `P.d (-2) (-1)`.
- The augmentation is `e : P ⟶ (single C (ComplexShape.up ℤ) 0).obj S.X₃`,
  with `[QuasiIso e]`. The supplied degree-zero lift is `ell`; `hell` is
  `ell ≫ S.g = e.f 0`, transported by the canonical single-degree component iso.
  All these binders quantify over arbitrary supplied P, e and ell.
- The first existential gives `f : P.X (-1) ⟶ S.X₁`; the first equality is
  `f ≫ S.f = P.d (-1) 0 ≫ ell`. The next universal clause is precisely uniqueness
  among maps satisfying this factorization (not only among cocycles). The next
  clause is `P.d (-2) (-1) ≫ f = 0`.
- `fbar` has target the actual shift of N[0] by `(1 : ℤ)`. Its degree -1
  component, after the canonical shift and single-degree identifications, equals
  f. Its components at every other integer are zero. Being a complex morphism
  includes all cochain equations.
- The cone is the existing `mappingCone ((single C (ComplexShape.up ℤ) 0).map S.f)`.
  Its definition is Mathlib's homotopy cofiber: the biproduct of N[0] in degree
  r+1 and E[0] in degree r, with differential (-d_N, 0; i, d_E) in that order.
  Thus in degree -1 it is canonically N, in degree zero canonically E, elsewhere
  zero, and the surviving differential is i. This uses the existing construction,
  rather than introducing an arbitrary two-term complex or an uncharacterized cone.
- `kappa` is a morphism to that cone. Its degree -1 coordinate after
  `mappingCone.fst` and `singleObjXSelf` equals f; its degree-zero coordinate after
  `mappingCone.snd` and `singleObjXSelf` equals ell. The complementary coordinates
  map to zero objects, so these fix the entire components. Its components in all
  other degrees are explicitly zero.
- The canonical v is the literal `mappingCone.descShortComplex
  (S.map (single C (ComplexShape.up ℤ) 0))` everywhere it occurs. This is defined
  as `desc S.f 0 S.g`: zero on the shifted N summand, p on E. Hence it has exactly
  the stipulated degree-zero p, not merely an arbitrary quasi-isomorphism.
- `kappa ≫ mappingCone.descShortComplex ... = e` renders v kappa = e.
  Mathlib's `mappingCone.triangle ...` has third arrow induced by **minus**
  `mappingCone.fst`. Therefore the **negative** of its `mor₃` is exactly the
  projection pr of the node. `kappa ≫ (-...mor₃) = fbar` renders pr kappa = fbar
  with the requested sign.
- `QuasiIso (mappingCone.descShortComplex ...)` is the asserted quasi-isomorphism.
  `∀ r, r ≠ 0 → IsZero (...homology r)` includes degree -1 and every other
  nonzero integer. The following `IsIso` of `homologyMap v 0` composed with
  `singleObjHomologySelfIso ...` identifies H⁰ of the cone with X **through p**.
- `vIso` is an isomorphism in `DerivedCategory C` whose forward map is explicitly
  `DerivedCategory.Q.map v`. Its final equation is `Q.map kappa = Q.map e ≫ vIso.inv`,
  the categorical left-to-right rendering of Q(kappa) = Q(v)⁻¹ Q(e). The iso
  witness allows its inverse to be stated without assuming its invertibility
  separately as a hypothesis; the hom equation fixes the witness canonically.
- There is no projectivity, existence of projectives, boundedness below, or split
  extension assumption.

Dependency declarations read and used:

- def-sp-abelian: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (also supplied by the derived-category imports).
- def-weil-size-convention: its recorded metatheoretic convention, rendered by explicit
  universe levels u, v, w, not a second definition.
- def-weil-abstract-derived-category: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  cochain morphisms, homology and `QuasiIso` of its Mathlib framework.
- def-weil-pbc-exact-sequence: `CategoryTheory.ShortComplex.ShortExact` (fields
  `exact`, `mono_f`, `epi_g`), imported through its recorded module
  `Mathlib.Algebra.Homology.ExactSequence`.
- Proof dependency lem-weil-pbc-abelian-short-exact-kernel:
  `CategoryTheory.ShortComplex.ShortExact.fIsKernel`,
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact`, exposed by the imports.
- Proof dependency lem-weil-pbc-cochain-complexes-degreewise-exact:
  `HomologicalComplex.shortExact_iff_degreewise_shortExact` and the complex Abelian
  instance in `Mathlib.Algebra.Homology.HomologicalComplexAbelian` (plain proof import).
- Proof dependency lem-pc-cone-short-exact-quasi-iso:
  `CochainComplex.mappingCone.quasiIso_descShortComplex`,
  `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`. This is a public import
  because its `descShortComplex` is also part of the statement.
- Existing `HomologicalComplex.single`, `singleObjXSelf`,
  `singleObjHomologySelfIso` in `Mathlib.Algebra.Homology.SingleHomology` and its
  `Single` import; `CochainComplex.mappingCone.fst`, `snd`, and `triangle` in
  `Mathlib.Algebra.Homology.HomotopyCategory.MappingCone` / `Pretriangulated`;
  `CochainComplex.shiftFunctorObjXIso` in `HomotopyCategory.Shift`.

Sources checked: the current `literature/blueprint/latest/` direct-images proof,
paragraph (3), now gives the higher-level preservation argument and no longer
spells out this extracted internal normalization. The node retains its explicit
reviewed extracted statement. The component calculation follows the node's full
proof and the still-current Stacks `derived.tex`, definition-cone (014E), and the
construction immediately preceding lemma-derived-canonical-delta-functor (0152).
The latter explicitly uses the negative cone projection. No source-based change
to the mathematical statement was needed.

Edge cases checked: all three objects zero; N = 0 (the inclusion has zero source);
X = 0 (an acyclic augmentation); P supported only in degree zero; arbitrary
nonprojective P with infinitely many negative degrees; the r = -2, -1, 0, 1 chain
equations and the degree-zero versus nonzero cohomology cases. In each case the
kernel factorization and component descriptions retain their literal meaning.
Independent category and localization universes are retained. The canonical
biproduct/single/shift isomorphisms avoid asserting literal object equality for
chosen categorical constructions.

Searches (all with the prescribed `msearch.py Q101 <item>` wrapper unless marked rg):

- LeanFinder: `A lift of an augmentation through a short exact sequence defines a
  cocycle and a map to its mapping cone` — 8 hits, including `mappingCone.lift`,
  `liftCocycle`, and component lemmas. These require an already supplied compatible
  cocycle and do not state the kernel factorization or the whole result.
- Loogle: `CochainComplex.mappingCone.lift, CochainComplex.mappingCone.descShortComplex`
  — 0 hits for the combined query. Separate query `CochainComplex.mappingCone.lift`
  — 10 hits, the generic lift and its component identities, not this statement.
- Mathlib grep, subdirectory `Algebra/Homology`:
  `mappingCone.*lift|lift.*mappingCone|descShortComplex` — 22 hits, including the
  generic cone lift and the existing cone quasi-isomorphism used here.
- LeanSearch: `Given a lift from degree zero of an augmented complex through a short
  exact sequence there is a unique kernel cocycle and a map to the mapping cone`
  — 8 hits, again generic cone lift/cochain/cocycle identities, no exact whole match.
- rg of `lean/WeilConjectures` and `lean/Sheaf`:
  `augmented.*[Cc]one|extensionCone|augmentation.*lift|lem-sfb-augmented-resolution-extension-cone-lift`
  — unrelated augmentation/tower/CE constructions; no declaration for this item.
  Read `augmentationCone_lift` in EvaluationDualityCompletion: it concerns a limit
  cone of a tensor tower, not an extension cone.
- rg of `dag/lean_names_upstream.json`, Mathlib, WeilConjectures and Sheaf for the
  proposed full theorem basename — no name collision.

Validation: `scompile.py` compiled the file both as a sandbox module and under its
actual library module name, with no errors or warnings. An initial parser issue
around unary negative composition and a namespace qualification for the shift
component iso were repaired before this successful run. No local or global build.

## Second reading by Q101

The worker reread the node alongside the final module; the maintainer performs the
independent delivery review. In particular checked the direction of categorical
composition, uniqueness of f among all factorizations, shift by +1, the minus sign
on Mathlib's triangle arrow, and the prescribed two cone coordinates. The bundled
short complex retains the three arbitrary objects and both maps. The explicit
`descShortComplex` fixes v through p, and the zero-degree homology morphism is to X,
not to an unrelated isomorphic object. The localization statement includes an
actual isomorphism with prescribed hom and its inverse equation, not just
cohomology isomorphisms. Every hypothesis and conclusion is matched above. No
additional mathematical mismatch was found; no statement correction was made.
