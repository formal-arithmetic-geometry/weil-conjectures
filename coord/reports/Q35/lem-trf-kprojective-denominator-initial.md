## Worker report

Item: `lem-trf-kprojective-denominator-initial`. The new module is
`Sheaf.CategoryTheory.DerivedCategory.KProjectiveDenominatorInitial`.
Its main declaration is `CochainComplex.IsKProjective.denominator_initial`.
The node is unchanged except for `lean`. No new nodes, dependency repairs,
statement correction, or disputed statement are needed.

The two helper definitions contain real data: `identityQuasiIsoDenominator P`
is `MorphismProperty.Over.mk` of the identity, certified by `id_mem`;
`quasiIsoDenominatorDiagram P F` is exactly the two forgetful functors composed
with `F`. They merely name canonical objects used repeatedly by the statement;
they do not introduce another definition of denominators, homotopy, localization,
or essential constancy. The only postponed proof is the named main theorem.
Its docstring contains all three proof steps of the node.

Clause-by-clause rendering:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| An abelian category A | `{A : Type u} [Category.{v} A] [Abelian A]` |
| Its homotopy category and derived localization | `HomotopyCategory A (ComplexShape.up ℤ)`, `DerivedCategory.Qh`, with `[HasDerivedCategory.{w} A]` retaining the chosen morphism universe |
| P is an integer cochain complex, K-projective in the stated homotopy-to-zero sense | `(P : CochainComplex A ℤ) [P.IsKProjective]`; Mathlib's class quantifies over every acyclic complex and every map, and asks for `Nonempty (Homotopy f 0)` |
| Incoming quasi-isomorphisms, arrows all commuting triangles | `(HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Over ⊤ ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)`; `⊤` puts no further restriction on horizontal arrows |
| This category is cofiltered | The first conjunct is `IsCofiltered` of precisely this category |
| The identity denominator is initial | `∃ h : IsInitial (identityQuasiIsoDenominator P), ...` |
| For every s there is a unique section t_s | Define the displayed section by the term `(h.to s).left`; the first inner conjunct states `(h.to s).left ≫ s.hom = 𝟙 _` and quantifies over every possible `t` to assert uniqueness |
| Q_h(t_s) is the inverse of Q_h(s) | The second inner conjunct equates `DerivedCategory.Qh.map (h.to s).left` with `(Localization.isoOfHom DerivedCategory.Qh ... s.hom s.prop).inv`; `isoOfHom` has forward map exactly `Qh.map s.hom` |
| u t_s = t_s' for each denominator arrow | The third inner conjunct states `(h.to s).left ≫ a.left = (h.to s').left` for every arrow `a : s ⟶ s'` |
| Any category H and any functor F | `∀ (H : Type uH) (_ : Category.{vH} H) (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)`; the universes are independent of u, v and w and F has no extra properties |
| The diagram G(s) = F(Y) is essentially constant with value F(P) | `IsEssentiallyConstantProDiagram (quasiIsoDenominatorDiagram P F) (F.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P))` |
| A witnessing cone with legs F(t_s) | The existential `c` is a natural transformation from the constant diagram at F(P) to G; `∀ s, c.app s = F.map (h.to s).left` fixes every leg |
| Identity leg at the identity denominator | `c.app (identityQuasiIsoDenominator P) = 𝟙 _` |
| Retraction r is the identity at this stage | Existential `r : F(P) ⟶ F(P)`, together with `r = 𝟙 _` and `c.app (identityQuasiIsoDenominator P) ≫ r = 𝟙 _` |
| Common stage is the identity denominator for every s | The final equality is the exact factorization criterion at `k = j₀ = identityQuasiIsoDenominator P`, `a = 𝟙 (identityQuasiIsoDenominator P)`, `b = h.to s`: `G.map (h.to s) = G.map (𝟙 ...) ≫ r ≫ c.app s` |

Lean composition is diagrammatic: `t_s ≫ s` renders the node's `s t_s`.
The last existential supplies the same cone, stage and retraction that witness
the essential-constancy predicate, rather than an unrelated cone. The types
of G at the identity denominator reduce to F(P) by the actual helper definitions.
Using `IsInitial.to` provides the sections as data from a uniqueness property;
no object is chosen from an undetermined existence theorem.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; its class docstring matches the
  node's preadditive, normal mono/epi, kernel/cokernel description.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Qh`, `HomotopyCategory.quotient` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` and its imports. The Qh
  localization instance is used by `Localization.isoOfHom`.
- `def-pur-saturated-triangulated-localization`:
  `WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`.
  Its `Functor.IsTriangulatedLeftDerivedValue` docstring and definition specify
  exactly `MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F` as the
  denominator diagram. This same existing interface is used directly, without
  imposing the extra triangulated-target conditions of that derived-value predicate.
- `def-pc-essentially-constant-pro-diagram`:
  `CategoryTheory.IsEssentiallyConstantProDiagram` from
  `WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro`.
  Its full body was read: cofilteredness, natural cone, retraction and common
  earlier-stage factorization all have the directions used here.
- Proof input `lem-coef-kprojective-derived-hom-bijection`:
  `CochainComplex.IsKProjective.Qh_map_bijective` from
  `Mathlib.Algebra.Homology.DerivedCategory.KProjective`, imported as a proof
  dependency. The full signature needs only K-projectivity of the source P.
- The supporting `CochainComplex.IsKProjective` class was read in
  `Mathlib.Algebra.Homology.HomotopyCategory.KProjective`. Its `Homotopy`
  definition in `Mathlib.Algebra.Homology.Homotopy` has the equation
  `f.f i = dNext i hom + prevD i hom + g.f i`, which is exactly f-g=dh+hd.
- `MorphismProperty.Over.mk`, `.Over`, `.Over.forget`, `.Over.w` and the
  unrestricted horizontal property were read in
  `Mathlib.CategoryTheory.MorphismProperty.Comma`.
- `IsInitial.to` and `Localization.isoOfHom` were read in
  `Mathlib.CategoryTheory.Limits.Shapes.IsTerminal` and
  `Mathlib.CategoryTheory.Localization.Predicate`, respectively.

Sources checked directly: local `literature/stacks-project/derived.tex`,
Situation `situation-derived-functor` and Definition
`definition-right-derived-functor-defined` (Tags 05S8, 05S9), and
`literature/stacks-project/categories.tex`, Definition
`definition-essentially-constant-diagram` (Tag 05PU), especially its part (2).
The node explicitly identifies the section argument as an agent-written expansion;
the module attributes it accordingly, rather than claiming it is a Stacks lemma.

Edge cases checked mathematically before writing:

- P = 0: every homotopy-class map from P is zero; its identity is zero, so the
  section, localization and cone assertions remain valid.
- s = 1_P: uniqueness forces its section to be the identity, giving the stated
  identity cone leg and retraction.
- Y acyclic and noncontractible, with P = 0: the unique map 0 to Y is a section
  in K(A) of Y to 0. The statement does not claim the reverse composite is
  the identity in K(A), or that s is an isomorphism there.
- Neither Y nor any other denominator source is assumed K-projective.
  P can be unbounded and need not have termwise projective objects.
- F need not be additive, exact, triangulated, or preserve any limit. H has no
  zero-object or nonemptiness assumption; the presence of F itself supplies
  its actual values.
- The denominator category is never empty because the identity is constructed.
  Parallel arrows are equalized by the same initial stage.
- The independent object, morphism and derived-localization universes are
  retained. No smallness or equality of universes was added.

Searches (2026-10-24, prescribed `msearch.py` for Q35 and this item):

1. LeanFinder: `The identity denominator at a K-projective complex is initial
   and every functor on its incoming quasi-isomorphisms is essentially constant`.
   Eight hits: K-projectivity, its orthogonality characterization, projective
   resolutions, and `Qh_map_bijective`; none states this whole denominator result.
2. Loogle: `"IsKProjective", "Qh"`. One hit,
   `CochainComplex.IsKProjective.Qh_map_bijective`, used as the proof input.
3. Mathlib grep: `IsKProjective|denominator|IsInitial`, restricted to
   `Algebra/Homology/DerivedCategory/KProjective.lean`. Five hits, all
   K-projective namespace/hypothesis references; no initiality or cone statement.
4. LeanSearch: `The identity denominator of a K-projective complex is initial
   in its category of incoming quasi-isomorphisms and every functor gives an
   essentially constant pro diagram`. Eight hits, including the K-projective
   constructor and Qh localization instance, not this statement.
5. Direct project `rg` over both `lean/WeilConjectures` and `lean/Sheaf`:
   `kprojective-denominator-initial|[Kk][Pp]rojective.*[Dd]enominator|[Ii]sInitial.*[Dd]enominator`.
   Only explanatory mentions of the Hom-bijection input in derived-computation
   modules, with no declaration stating the result. The separately required
   `grep -rn 'lem-trf-kprojective-denominator-initial' lean/WeilConjectures`
   returned no match.
6. Direct searches for `IsEssentiallyConstantProDiagram` located the recorded
   predicate and existing generic pro-diagram results. These do not state
   K-projective initiality, unique sections and the specified witnesses together.
7. Proposed-name search in Mathlib and both project roots for
   `identityQuasiIsoDenominator|quasiIsoDenominatorDiagram|denominator_initial`
   returned no match.

Validation: `scompile.py Q35 lem-trf-kprojective-denominator-initial <module>`
compiled the sandbox and library forms cleanly (1.6 seconds each). The dry run
then compiled the final form including the explicit Abelian import and printed
`OK (dry run)`: the server preflight and per-file compiler both pass.
`set_option autoImplicit false` is active; all universes are declared.

## Second reading by Q35

This is an in-thread rereading of the node and final module, not a claim of an
independent worker review: the dispatcher explicitly forbids starting agents.
The maintainer's independent review remains the delivery review in this workflow.

I checked each binder against the node: general abelian A, chosen derived
universe, exactly K-projective P, and completely unrestricted H and F.
I checked that the denominator arrows use `⊤`, not a quasi-isomorphism
restriction, and that `(h.to s).left` has source P and target s.left.
The section equation and its uniqueness are in K(A), while only the inverse
equation uses Qh. The naturality equation is diagrammatic `t_s ≫ a.left = t_s'`.
For the final witnesses, c is a cone rather than a cocone, its fixed value is
F(P), the retraction has direction G(1_P) to F(P), and the transition
factorization starts at the identity stage with its identity arrow. Every
clause of the existing pro-diagram predicate is explicitly witnessed.
No mismatch or statement correction was found. An explicit public import of
the recorded Abelian module was added during this check.
