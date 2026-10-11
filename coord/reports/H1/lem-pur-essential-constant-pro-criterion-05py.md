## Worker report

The module `lean/Sheaf/CategoryTheory/DerivedCategory/EssentiallyConstantProCriterion.lean`
states `CategoryTheory.homColimit_essentiallyConstantProDiagram`. Its sole proof is
`sorry`; it adds no definitions. The declaration docstring contains all four proof steps.

Hypotheses and clauses, matched to the node:

- A category J and category C: `{J : Type uJp} {C : Type uCp}` with
  `[Category.{vJp} J] [Category.{vCp} C]`. All four universes are explicitly declared.
- J cofiltered: `[IsCofiltered J]`.
- Diagram G, value X, chosen index and arrow: `(G : J ⥤ C) (X : C) (j₀ : J)` and
  `(r : G.obj j₀ ⟶ X)`.
- For every W, the indicated map is bijective: `h : ∀ (W : C), Function.Bijective ...`.
  The function sends `φ : X ⟶ W` to
  `(G.op ⋙ yoneda.obj W).ιColimitType (Opposite.op j₀) (r ≫ φ)`.
  The diagram is over Jᵒᵖ; its objects are `G.obj j ⟶ W`, and its arrows precompose
  with G's transition maps. `Functor.ιColimitType` takes the class of a representative
  in Mathlib's quotient colimit of sets; no alternative colimit notion is defined.
- G essentially constant with value X: `IsEssentiallyConstantProDiagram G X`, exactly
  the dependency's recorded predicate, including cofilteredness, a cone, an index,
  a retraction and common-earlier-stage factorization.
- Natural cone maps: `∃ (u : (Functor.const J).obj X ⟶ G)`. This natural transformation
  has legs `u.app j : X ⟶ G.obj j`; its naturality is precisely the cone equation.
- The given retraction: `u.app j₀ ≫ r = 𝟙 X`.
- The cone-map characterization: for every j the class of `r ≫ u.app j` at j₀
  equals the class of `𝟙 (G.obj j)` at j. These are the displayed `ιColimitType`
  equations. Injectivity in `h (G.obj j)` makes each characterized leg unique;
  the universal class equation also supplies the common-stage factorization for
  this same cone. Thus the displayed cone is the cone exhibiting essential constancy,
  even though the predicate internally existentially binds its witnesses.

Dependency used: module `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`,
declaration `CategoryTheory.IsEssentiallyConstantProDiagram`. Read its full signature
and docstring and the entire definition from the recorded module. Mathlib declarations
used are `CategoryTheory.yoneda` (Mathlib.CategoryTheory.Yoneda), `Functor.op`,
`Functor.comp`, and `CategoryTheory.Functor.ιColimitType`
(Mathlib.CategoryTheory.Limits.Types.ColimitType). The full quotient and coprojection
definitions were read; the quotient lives in `Type (max uJp vCp)` without imposing
smallness on J relative to C's morphisms.

Edge cases checked: an empty J is excluded by the stated cofilteredness (and also
cannot supply j₀). Empty C cannot supply X. A one-object terminal diagram gives the
usual representable Hom bijection. In a category with zero objects there is no
additional nonzero assumption; identity classes and the retraction equation still
make sense. Independent index, index-Hom, object and Hom universes are retained;
no existence-of-colimit or smallness binder is added. No statement is disputed.

Searches performed:

- `msearch.py ... leanfinder "A cofiltered diagram is essentially constant with value X
  if Hom(X,W) maps bijectively to the filtered colimit of Hom(G(j),W) for every W"`:
  eight hits, concerning `IsCofiltered.IsEventuallyConstant`,
  `IsFiltered.IsEventuallyConstant`, `Functor.IsEventuallyConstantTo/From` and
  cofiltered initiality criteria. These are eventual-isomorphism or initial-functor
  statements, not the retraction-and-factorization pro-object criterion.
- `msearch.py ... loogle "CategoryTheory.Functor.IsEventuallyConstantTo,
  CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff"`: OK, zero hits.
- `msearch.py ... grep "essentially constant|IsEssentiallyConstantProDiagram|
  IsEventuallyConstantTo" CategoryTheory`: five hits in Mathlib's
  `Limits/Constructions/EventuallyConstant.lean`, no matching theorem.
- `rg` for `EssentiallyConstant|essentially constant|pro.*diagram` in WeilConjectures
  and lean/Sheaf: the existing predicate modules, specialized inverse systems and
  downstream uses were found; no converse Hom-colimit criterion module.
- `rg` for the item id in WeilConjectures: no hits. `rg` for the new theorem name
  in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no hits.
  The forward theorem node `lem-pc-essentially-constant-pro-hom-colimit` was also
  read and does not duplicate this converse.

The Stacks source checkout is absent on this machine. I opened the official pages
[05PY](https://stacks.math.columbia.edu/tag/05PY),
[05PZ](https://stacks.math.columbia.edu/tag/05PZ) and
[05PU](https://stacks.math.columbia.edu/tag/05PU). The node correctly uses the pro
dual of 05PY; 05PZ states it directly. No node correction or dependency module is needed.

Validation: `scompile.py H1 lem-pur-essential-constant-pro-criterion-05py <module>`
compiled the final module in 1.1 seconds, exit 0, no warnings. The dry delivery check
is run after the node record and this report are complete. The second reader supplies
the independent second-reading section and delivers; the worker does not push.

## Second reading by H1

I independently compared the node statement with the Lean declaration
`CategoryTheory.homColimit_essentiallyConstantProDiagram` in
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion`.

- The cofiltered index category `J` and category `C` render as `{J : Type uJp}`,
  `{C : Type uCp}`, `[Category.{vJp} J]`, `[Category.{vCp} C]`, and
  `[IsCofiltered J]`; all four universes are bound.
- The diagram, value, chosen index, and retraction render as
  `(G : J ⥤ C) (X : C) (j₀ : J) (r : G.obj j₀ ⟶ X)`.
- The universal hypothesis renders as `∀ W, Function.Bijective (...)`, with
  `φ : X ⟶ W` sent to the `Functor.ιColimitType` class of `r ≫ φ` at
  `Opposite.op j₀`. This is exactly the node's class of `φ ∘ r` in the
  colimit over `Jᵒᵖ`.
- The conclusion's first conjunct is
  `IsEssentiallyConstantProDiagram G X`, the recorded definition dependency;
  it supplies the cone, retraction, and common-stage factorization required by
  the node. The second conjunct existentially supplies
  `u : (Functor.const J).obj X ⟶ G`, states `u.app j₀ ≫ r = 𝟙 X`, and for
  every `j` equates the class of `r ≫ u.app j` at `j₀` with the class of
  `𝟙 (G.obj j)` at `j`. These are exactly the node's characterization clauses.

No mismatch was found and no source or dependency correction was necessary.
The empty-index case is excluded by the cofiltered instance and the explicit
`j₀`; empty `C` cannot provide `X`; one-object diagrams and zero morphisms are
covered without extra assumptions; `n = 0` and characteristic conditions are
irrelevant to this categorical statement. Independent object, hom, and index
universes are retained, with no smallness or colimit-existence assumption.

Searches were rechecked with `rg` in the project and source trees and with the
recorded LeanFinder/Loogle/grep searches: only the separate
`IsEssentiallyConstantProDiagram` definition and Mathlib eventual-constancy
notions exist; no duplicate converse criterion exists. The source place is
Stacks Categories, Tag 05PY (dual pro implication (4) => (1)), also 05PZ.
The module compiles cleanly with `scompile.py`; no warnings occur beyond the
intentional `sorry` proof.
