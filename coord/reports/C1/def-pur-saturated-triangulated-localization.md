## Worker report

The module `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem` defines the node's multiplicative system, saturation, triangulated compatibility, strict localization, and pointwise left-derived definedness and value. All six declarations are full Prop-valued definitions; there are no proofs, axioms, or sorries. The original node is unchanged except for its Lean record. No new nodes or dependency modules are required: all notions introduced here are explicitly introduced by this item itself.

Hypotheses and clauses, in order:

- A triangulated category D is rendered by `Category.{v} C`, `HasZeroObject C`, `HasShift C ℤ`, `Preadditive C`, additive integer shifts, `Pretriangulated C`, and `CategoryTheory.IsTriangulated C`. These are exactly the dependency's Mathlib realization of TR1--TR4; finite biproducts are supplied by pretriangulation. `S : MorphismProperty C` is a set of morphisms with arbitrary endpoints.
- MS1: both fraction-calculus classes extend `S.IsMultiplicative`, whose fields give identities and composition. This is more than Mathlib's bare `IsMultiplicative`, which would omit MS2 and MS3; `IsMultiplicativeSystem` uses the conjunction of both calculus classes.
- MS2, first direction: `HasLeftCalculusOfFractions.exists_leftFraction` turns the right fraction with denominator t and numerator g into a left fraction with denominator s and numerator f, with equality `g ≫ s = t ≫ f`. Second direction: `HasRightCalculusOfFractions.exists_rightFraction` supplies the reversed completion and equality `g ≫ s = t ≫ f`.
- MS3, first direction: `HasLeftCalculusOfFractions.ext` changes equality after a denominator into equality before a denominator; its input equality is `t ≫ f = t ≫ g` and its output is `f ≫ s = g ≫ s`. The right-calculus `ext` field is the opposite implication.
- MS4: `IsSaturatedMultiplicativeSystem` explicitly quantifies four objects, `h : A ⟶ B`, `g : B ⟶ C'`, and `f : C' ⟶ D`, with `S (g ≫ f) → S (h ≫ g) → S g`. Lean's left-to-right composition exactly reverses the printed order of the node's `f ∘ g` and `g ∘ h`.
- MS5: `S.IsCompatibleWithTriangulation` extends `S.IsCompatibleWithShift ℤ`, whose condition is invariance under each integer shift; at 1 it is exactly the node's iff. Conversely the shift-by-one iff implies the integer-shift version by iteration and inverse shift. Coherence isomorphisms do not alter membership: MS4 implies that all isomorphisms are in S, and MS1 gives composition stability. Thus this existing Mathlib notion has the same content, rather than an extra hypothesis.
- MS6: `IsCompatibleWithTriangulation.compatible_with_triangulation` quantifies two triangles, both distinguished, maps a and b in S, and `T₁.mor₁ ≫ b = a ≫ T₂.mor₁`; it supplies c in S with `T₁.mor₂ ≫ c = b ≫ T₂.mor₂` and `T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃`. These are the two remaining squares, with s=a, s'=b, s''=c.
- Localization: `IsStrictLocalizationAt Q S` requires `S.IsInvertedBy Q`. For each target E (independent arbitrary universes uE, vE), `Nonempty (Localization.StrictUniversalPropertyFixedTarget Q S E)` supplies existence and uniqueness of functor factorization with equality, hence precisely the node's bijection of functors. Its `lift`, `fac`, `uniq` fields give surjectivity and injectivity, with inverting functors viewed as a subtype. `Function.Bijective (fun α : G ⟶ G' ↦ whiskerLeft Q α)` is exactly the asserted bijection of natural transformations. The usual `Q.IsLocalization S` only asks for equivalence and is therefore deliberately not substituted for this stricter clause.
- Situation 05S8: the two left-derived predicates bind both C and D with the full triangulated instances, F with `F.CommShift ℤ` and `F.IsTriangulated`, and `hS : S.IsSaturatedTriangulatedMultiplicativeSystem`. By the dependency's `Functor.IsTriangulated` declaration, F is additive as well as preserving distinguished triangles. These binders express the situation without introducing a second structure for it.
- S/X: `MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F` is the diagram on `S.Over ⊤ X`. An object is an arrow into X satisfying S; a morphism is any commuting triangle. The second morphism property is top, not S: there is no additional denominator condition on a triangle's connecting map. The diagram sends the arrow from X' to F(X') and its connecting map to F of that map.
- LF defined at X: `IsTriangulatedLeftDerivedDefinedAt` is `∃ Y : D, F.IsTriangulatedLeftDerivedValue S hS X Y`.
- LF value Y: `IsTriangulatedLeftDerivedValue` is the recorded `IsEssentiallyConstantProDiagram` on this diagram, with the SAME Y as its value. That predicate includes cofilteredness and precisely the cone, retraction, and common-earlier-stage factorization. The node names a value, not a canonically chosen representative, so no choice of an object called LF(X) is introduced.

Dependency declarations read and used:

- `def-weil-triangulated-category` is a Mathlib leaf. Read `Mathlib.CategoryTheory.Triangulated.Pretriangulated` / `CategoryTheory.Pretriangulated`, `Mathlib.CategoryTheory.Triangulated.Triangulated` / `CategoryTheory.IsTriangulated`, and `Mathlib.CategoryTheory.Triangulated.Functor` / `CategoryTheory.Functor.IsTriangulated`, including their signatures and docstrings. The main localization import provides them transitively.
- `def-pc-essentially-constant-pro-diagram`: import `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`, declaration `CategoryTheory.IsEssentiallyConstantProDiagram`; its full signature and body were read. The value is an explicit parameter and cofilteredness is a conjunct.
- Mathlib primitives reused: `MorphismProperty.HasLeftCalculusOfFractions`, `HasRightCalculusOfFractions` in `Localization.CalculusOfFractions`; `IsCompatibleWithTriangulation` in `Localization.Triangulated`; `Localization.StrictUniversalPropertyFixedTarget` in `Localization.Predicate`; and `MorphismProperty.Over` / `Over.forget` in `MorphismProperty.Comma`.

Source checked directly in the available Stacks checkout `/home/ubuntu/c1-stacks-review/categories.tex` (multiplicative systems, saturation, right-localization arrows) and `derived.tex` (triangulated compatibility, Situation derived-functor, Definition right-derived-functor-defined, part 2). The repository's untracked Stacks checkout is absent; these files supply the cited source text. No node fault or statement correction was needed.

Edge cases: identities ensure S/X is nonempty at every X, including the zero object; S cannot be the empty morphism property on a nonempty category. The indiscrete property S=top satisfies saturation and both compatibility clauses. Isomorphisms satisfy MS4 (the middle map has both inverses). A noninvertible middle map need not follow merely from one composite in S, so the definition keeps both antecedents. Zero objects and zero categories impose no nonzero-object hypothesis. No smallness, skeleton, or countability restriction is placed on C, D or the target category; object and hom universes are separately explicit. For F=identity and denominators consisting of isomorphisms, the pro-diagram has value X. A value Y remains explicit, allowing all isomorphic representatives. The strict localization predicate retains equality of factorizations, matching the node's stronger strict wording.

Searches performed before writing:

- `msearch.py ... leansearch "saturated multiplicative system triangulated category"`: unavailable (Internal Server Error); no mathematical verdict assigned to the failed service.
- `msearch.py ... leanfinder "saturated multiplicative system compatible with triangulated structure localization"`: eight hits, the ObjectProperty trW calculus instances and triangulated-localization constructions; none gives the whole node's definition or Stacks MS4.
- `msearch.py ... loogle "MorphismProperty.HasLeftCalculusOfFractions, Localization.StrictUniversalPropertyFixedTarget"`: zero hits, service reports unknown identifier for the unqualified calculus name. Direct source inspection found the qualified declarations and they are used.
- `msearch.py ... grep "IsSaturated|Saturated|StrictUniversalProperty|def Over" CategoryTheory/Localization`: 25 hits, primarily strict universal property in Prod, Opposite, Quotient, Composition and CalculusOfFractions. These led to the reused strict universal property.
- Direct `rg` of Mathlib CategoryTheory found `IsCompatibleWithTriangulation` and integer shift compatibility, both reused, and `HasTwoOutOfThreeProperty` (different from literal MS4; not copied or substituted).
- Direct `rg` over `WeilConjectures` and `lean/Sheaf` for saturation, multiplicative-system names and essentially-constant/left-derived names found existing general derived-functor APIs, the project's essentially-constant predicates and related theorems, but no declaration of this node's compound definitions. `grep -rn "def-pur-saturated-triangulated-localization" WeilConjectures` found no tagged declaration.
- Direct `rg` for all six chosen names across Mathlib, `WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: no collisions.

Validation: the server single-file compiler returned exit code 0 with no warnings. The final dry-run preflight and compile are run after creating this report and the exact node signature.

## Second reading by C1

I independently matched the node clause by clause with the Lean declarations. The triangulated
category is rendered by `Category`, `HasZeroObject`, `HasShift ℤ`, `Preadditive`, additive shifts,
`Pretriangulated`, and `IsTriangulated`; `S` is a `MorphismProperty`. This introduces exactly the
objects and hypotheses of the node, with no finiteness, smallness, Noetherian, characteristic, or
universe restriction. `IsMultiplicativeSystem` is the conjunction of left and right calculus of
fractions, giving MS1--MS3. `IsSaturatedMultiplicativeSystem` adds the four-object MS4 implication
with composition order translated by Lean's `≫`. `IsSaturatedTriangulatedMultiplicativeSystem`
adds Mathlib's shift invariance and distinguished-triangle completion, which render MS5 and MS6.

`Functor.IsStrictLocalizationAt` introduces `Q`, `S`, every target category `E`, the strict
factorization universal property, and bijectivity on whiskered natural transformations; this is
the node's strict localization clause. `IsTriangulatedLeftDerivedValue` uses the diagram
`MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F` and the same explicit value `Y` in
`IsEssentiallyConstantProDiagram`; `IsTriangulatedLeftDerivedDefinedAt` existentially quantifies
that value. The derived-functor binders include both triangulated categories, exact/triangulated
functor structure, and the saturated system exactly as in Situation 05S8.

Edge cases checked: identities and the zero object are permitted; `S = ⊤`, isomorphism systems,
zero categories, arbitrary target universes, and explicit noncanonical isomorphic values `Y` remain
covered. The empty morphism property is correctly excluded by MS1 in a nonempty category. No
additional node or dependency module was needed. Searches in Mathlib, `WeilConjectures`, `lean/Sheaf`,
and upstream-name records found no duplicate compound definition; the qualified calculus,
triangulation, strict-universal-property, and essentially-constant declarations used here are the
recorded dependencies. The file compiled cleanly with `scompile.py`; no mismatch was found and no
Lean or node change was required beyond the worker's recorded `lean` entry.
