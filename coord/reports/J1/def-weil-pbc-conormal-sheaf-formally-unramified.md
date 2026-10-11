## Worker report

The module `Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal` defines
`AlgebraicGeometry.formallyUnramifiedConormal` for a chosen universal thickening and states
`AlgebraicGeometry.formallyUnramifiedConormal_independent`, with proof `sorry`. No definition
contains a `sorry`, and no theorem is proved in this delivery. No node correction or new node
is needed.

Clause-by-clause rendering:

- Schemes and morphism `h : Z → X`: `{Z X Z' : Scheme.{u}} (h : Z ⟶ X)`.
  Formal unramifiedness is `[FormallyUnramified h]`, the recorded Mathlib notion.
- A chosen universal first order thickening, closed immersion `i`, and structure map `h'`:
  `(i : Z ⟶ Z') (h' : Z' ⟶ X) (_H : IsUniversalFirstOrderThickening h i h')`.
  This predicate includes `IsFirstOrderThickening i`, hence `IsClosedImmersion i`,
  `i.ker ^ 2 = ⊥`, the equality `i ≫ h' = h`, and the universal lifting property for
  arbitrary schemes. No extra instance or affine hypothesis is imposed.
- Existence: the first conjunct of `formallyUnramifiedConormal_independent` is
  `∃ (Z') (i) (h'), IsUniversalFirstOrderThickening h i h'`. Its proof plan uses the
  recorded `FormallyUnramified.exists_universalFirstOrderThickening` theorem.
- The defining ideal sheaf is `i.ker`, converted to an actual module sheaf by the
  source's `i.ker.toModules`. No private copy of the ideal sheaf is introduced.
- The conormal module is exactly `(Scheme.Modules.tensorPullback i).obj i.ker.toModules`.
  This selects the node's displayed `i* I` expression. The equality with `i*(I/I²)`
  uses the square-zero clause already present in the universal-thickening hypothesis;
  the quotient by the zero submodule is canonically the ideal module itself. As in
  the project's CONORMAL SHEAF convention, tensor pullback of the ideal is also the
  closed immersion's conormal module, with affine sections `I/I²`.
- Independence under the unique compatible thickening isomorphism: the theorem gives
  `∃! φ, φ ≫ h₂ = h₁ ∧ i₁ ≫ φ = i₂`, and asserts `IsIso φ` for every compatible map.
  For each compatible `φ`, it gives `∃! e : C₂ ≅ C₁` satisfying the ideal-section equation.
  For sections `s₂` of `I₂` and `s₁` of `I₁` on `φ ⁻¹ᵁ U`, the premise
  `i₁.ker.toModulesι.app _ s₁ = φ.app U (i₂.ker.toModulesι.app U s₂)` says that `s₁`
  is the image of `s₂` under the scheme comparison. The conclusion says that `e.hom`
  sends the pulled-back class of `s₂` to that of `s₁`. Both classes are restricted
  to any common open `W` by `.val.map (homOfLE _).op`. The units are the canonical
  tensor-pullback units from `exists_tensorPullbackAdjunction`, not arbitrary maps.
  This pins uniqueness to the induced isomorphism; an assertion that all module
  isomorphisms are unique would be false when the conormal module has automorphisms.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`:
  `AlgebraicGeometry.FormallyUnramified`, with `hom_ext` and `of_hom_ext` providing
  its agreement with the node's affine square-zero uniqueness condition.
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening`:
  `AlgebraicGeometry.IsUniversalFirstOrderThickening` and its `.unique` theorem.
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists`:
  `AlgebraicGeometry.FormallyUnramified.exists_universalFirstOrderThickening`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `AlgebraicGeometry.Scheme.Hom.ker`;
  its signature and `ker_apply` were read. The source bridge
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` supplies
  `AlgebraicGeometry.Scheme.IdealSheafData.toModules` and `.toModulesι`.
- `Sheaf.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, the recorded module pullback.
  `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` supplies the canonical unit
  through `AlgebraicGeometry.Scheme.Modules.exists_tensorPullbackAdjunction`;
  its full statement and docstring were read.

Edge cases checked: empty schemes are permitted; no nonempty, finite-type, separated,
Noetherian, or characteristic assumption is imposed. A zero ideal gives a zero conormal
module by the formula. Nontrivial square-zero ideals are retained. All schemes, test
schemes and sheaves use the same explicit universe `u`, as the recorded universal
thickening predicate does. The construction is not restricted to affine schemes.
For nonzero conormal modules, possible scalar automorphisms explain why the section
compatibility condition is essential in the uniqueness statement.

Searches for an existing notion:

- `msearch.py ... leanfinder "conormal sheaf of formally unramified scheme morphism
  universal first order thickening"`: eight hits, all formal-unramified/étale facts,
  no conormal definition for universal thickenings.
- `msearch.py ... loogle "conormal"`: no hits, unknown identifier `conormal`.
- `msearch.py ... leansearch "conormal sheaf universal first order thickening"`:
  service unavailable (Internal Server Error); recorded as unavailable, no verdict.
- `msearch.py ... grep "conormal|Conormal" AlgebraicGeometry`: no Mathlib hits.
- `rg` in the source's `WeilConjectures`: no universal-thickening conormal definition;
  the algebraic-geometry hit in `DeformationToNormalCone.lean` is only a docstring.
  Searching the item id in the source and `dag/lean_names_upstream.json` found no match.
- `rg` in `lean/Sheaf`: `affine_conormal_sections` and closed-immersion functoriality
  are statements about `(tensorPullback i).obj i.ker.toModules`, not definitions for
  a chosen universal thickening; `diagonalConormal` concerns a different morphism.
  These searches confirm the existing ideal/pullback conventions and no duplicate
  definition of this node's notion.

Source checked directly: https://stacks.math.columbia.edu/tag/04F4, item (2), defines
this as the conormal sheaf in the universal thickening; https://stacks.math.columbia.edu/tag/01R2
provides the closed-immersion conormal convention. Local Stacks TeX is absent on this
machine, so the official pages were read. No STATEMENT-DISPUTED issue found.

Validation: the final substantive module compiled cleanly on the server in 2.7 seconds
with exit code 0. The final edit only expands the natural-language uniqueness proof.
The required dry run is run next; the independent second reader supplies their own
reading and delivery.

## Second reading by J1

I read the node statement and the module independently against Stacks 04F4 (2),
04F2/04F3, and 01R2. The introduced objects render as follows: the schemes and
map are `{Z X Z' : Scheme.{u}}`, `h : Z ⟶ X`, with `[FormallyUnramified h]`;
the chosen thickening is `i : Z ⟶ Z'`, `h' : Z' ⟶ X`, and
`_H : IsUniversalFirstOrderThickening h i h'`; its existence is the first
conjunct of `formallyUnramifiedConormal_independent`. The ideal sheaf is
`i.ker.toModules`, using the recorded `Scheme.Hom.ker` and its project
`toModules` conversion. The conormal module is exactly
`(Scheme.Modules.tensorPullback i).obj i.ker.toModules`, which is the node's
`i^*(I/I^2) = i^* I` under the square-zero clause in `_H`. Independence is
rendered by `IsUniversalFirstOrderThickening.unique` and the following unique
module isomorphism `e`; its section equation explicitly expresses compatibility
with the induced ideal-sheaf map and its restrictions to a common open.

The hypotheses match one-for-one: no affine, separated, finite-type, Noetherian,
characteristic, nonempty, or finiteness assumption is added, and all universes
are the single `u` of the node. Every conclusion clause is present, with the
quantifier order `Z₁ Z₂ i₁ h₁ i₂ h₂ H₁ H₂`, then the unique scheme comparison,
its isomorphism instance, and the uniquely characterized module isomorphism.
The stronger-looking section equation is the explicit form of the node's
“compatible with i” canonical isomorphism, so it does not add a mathematical
hypothesis or weaken the definition. I found no mismatch and changed nothing.

Edge cases were checked: empty schemes and zero ideals are admitted; square-zero
nonzero ideals remain; no characteristic or `n` parameter occurs; and the same
universe covers all test schemes. Searches (LeanFinder/Loogle/LeanSearch and
grep in Mathlib, `WeilConjectures`, and `lean/Sheaf`) found no existing
universal-thickening conormal declaration; nearby affine conormal statements and
`diagonalConormal` are different notions. The only validation change was this
independent review; the module still compiles with only its theorem `sorry`.
