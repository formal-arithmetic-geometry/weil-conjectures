## Worker report

Item: `lem-sf-invertible-factor-hom-cancellation`, group NF, stage 2, 2026-10-17.

The module `Sheaf.CategoryTheory.InvertibleFactorHomCancellation` states the whole node as
`CategoryTheory.MonoidalClosed.invertibleFactorHomCancellation`, with `sorry` as its entire
proof. Its helper `CategoryTheory.MonoidalClosed.ihomTensorBoth` constructs the node's map
`s` by an actual evaluation transpose. The map `t` is the upstream
`CategoryTheory.MonoidalClosed.ihomTensorToIhom`, not a new definition. No theorem is proved.
Only the item's `lean` field changes. No new node, dependency repair or statement correction
is needed. No statement dispute was found.

The source was read in `literature/stacks-project/categories.tex`,
`lemma-invertible` (Tag 0FFM, lines 9267–9295), and
`remark-internal-hom-monoidal` (Tag 0GWJ, lines 9615–9664). The former gives the tensor
equivalence from two inverse-factor isomorphisms. The latter gives the right-tensor
adjunction, its evaluation, and maps defined by evaluation transposes. The node is the
agent consequence of these sources described in its source field; its nine proof steps
are retained and rendered in the theorem's proof-plan docstring.

Hypothesis and clause correspondence:

1. A category with unrestricted object and morphism universes is
   `{C : Type u} [Category.{v} C]`, with `universe v u` explicit.
2. The node's monoidal structure is `[MonoidalCategory C]`, precisely the declaration
   recorded by `def-sfb-monoidal-category`. Tensor products, associators and unitors are
   the existing Mathlib ones; every suppressed associator needed by an equation is written.
3. The natural braiding, both hexagons and the symmetry identity are
   `[SymmetricCategory C]`, extending `BraidedCategory C`. Its braiding is `β_`.
4. The chosen closed structure is `[MonoidalClosed C]`, using `ihom`,
   `ihom.adjunction`, `curry`, and `pre` from Mathlib. Mathlib uses
   `Hom(X ⊗ Z,Y) ≃ Hom(Z,[X,Y])`. The node uses the equally general
   `Hom(Z ⊗ X,Y) ≃ Hom(Z,[X,Y])`. Symmetry changes one to the other: send a map
   `Z ⊗ X ⟶ Y` to `curry ((β_ X Z).hom ≫ f)`. Thus the node's right evaluation is
   `(β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y`.
   Conversely, any specified right-tensor adjunction in the node determines a Mathlib
   closed instance with the same right adjoint by this symmetry transport. This changes
   neither the chosen internal-Hom objects nor the mathematical hypothesis. The action
   in the first variable is `pre`, the adjunction-induced internal-Hom action; the
   assumed naturality in that variable identifies it with the node's action.
5. The two objects are `(J I : C)`. The two *specified* inverse-factor isomorphisms are
   `(a : J ⊗ I ≅ 𝟙_ C)` and `(b : I ⊗ J ≅ 𝟙_ C)`. No compatibility, exact pairing,
   triangle equation, or dualizability of `X` or `Y` is assumed.
6. The witnesses `t : ∀ X Y, [X,Y] ⊗ J ≅ [X,Y ⊗ J]` and
   `s : ∀ X Y, [X,Y] ≅ [X ⊗ J,Y ⊗ J]` are families of genuine isomorphisms.
   The first conjunct identifies their forward maps with `ihomTensorToIhom X Y J`
   and `ihomTensorBoth X Y J`, respectively. Consequently these witnesses carry the
   canonical maps and are uniquely determined, not arbitrary isomorphisms chosen
   from existence alone.
7. `ihomTensorToIhom` is the existing left-evaluation transpose
   `curry ((α_ _ _ _).inv ≫ (ihom.ev X).app Y ▷ J)`.
   Under symmetry transport it is exactly the node's right-evaluation transpose `t`:
   braiding naturality and the hexagon move `J` past `X`, and the two swaps of `X`
   with `[X,Y]` cancel by symmetry. The first equation of the second conjunct
   writes the node's first displayed uncurrying equation with the full permutation
   `(H ⊗ J) ⊗ X → H ⊗ (J ⊗ X) → H ⊗ (X ⊗ J) → (H ⊗ X) ⊗ J`.
8. `ihomTensorBoth` is the explicit transpose
   `(X ⊗ J) ⊗ H → X ⊗ (J ⊗ H) → X ⊗ (H ⊗ J) → (X ⊗ H) ⊗ J → Y ⊗ J`.
   Its right-evaluation form is precisely the second equation of the second conjunct:
   `(s X Y).hom ▷ (X ⊗ J)` followed by right evaluation equals
   `(α_ H X J).inv` followed by `e_{X,Y} ▷ J`.
9. The third and fourth equations of the second conjunct are the node's inverse
   evaluation normalizations. They compose `(t X Y).inv ▷ X` or
   `(s X Y).inv ▷ (X ⊗ J)` with the corresponding evaluation composite to obtain
   right evaluation at the target internal Hom.
10. The third conjunct quantifies over all `X X' Y Y'`,
    `(f : X' ⟶ X)` and `(g : Y ⟶ Y')`. The induced `[f,g]` is
    `(pre f).app Y ≫ (ihom X').map g`.
    Its first two equations are exactly the node's naturality equations for `t` and `s`;
    the tensoring of `f` and `g` uses `f ▷ J`, `g ▷ J`.
    Its final two equations give the corresponding variable naturality of both inverses.
11. The last conjunct quantifies over all `J' : C` and `(z : J ≅ J')`.
    The `t` identity is `H ◁ z.hom ≫ t_{J'} = t_J ≫ [1,Y ◁ z.hom]`.
    The `s` identity is `s_{J'} = s_J ≫ [X ◁ z.inv,Y ◁ z.hom]`.
    The two maps at `J'` are the same canonical definitions, with no additional
    inverse-factor choice. Every `J'` is automatically invertible by transport
    along `z`. This formulation expresses compatibility with every factor isomorphism,
    including those that have no relation to the specified data `a,b`.
    The identities also determine the inverse compatibility: from
    `P ≫ t_{J'} = t_J ≫ Q` obtain
    `t_{J'}⁻¹ ≫ P⁻¹ = Q⁻¹ ≫ t_J⁻¹`; from `s_{J'} = s_J ≫ R` obtain
    `s_{J'}⁻¹ = R⁻¹ ≫ s_J⁻¹`. Here `P,Q,R` are isomorphisms made from `z`, so
    inverse compatibility adds no additional mathematical assertion.
12. The canonical cancellation isomorphism `c` is `(s X Y).symm`. Its hom map is
    `(s X Y).inv`, appearing in the fourth evaluation equation and the final
    variable-naturality equation. The theorem therefore includes cancellation and
    its evaluation normalization, not only an abstract equivalence of Hom objects.

Dependency declarations read and used:

- `def-sfb-monoidal-category`: its status is `mathlib`, with match
  `CategoryTheory.MonoidalCategory` in `Mathlib.CategoryTheory.Monoidal.Category`.
  Read the structure at lines 87–107 and class at lines 162–210, including the
  chosen unit, tensor functor laws, structural naturality, pentagon and triangle.
  The recorded declaration supplies the actual `[MonoidalCategory C]` binder.
- Proof dependency `lem-sf-quasi-inverse-hom-bijection`: its status is `mathlib`.
  Its match is `CategoryTheory.Equivalence.fullyFaithfulFunctor` in
  `Mathlib.CategoryTheory.Equivalence`; read `Equivalence.mk` at lines 349–354,
  `fullyFaithfulFunctor` at lines 550–552, and `FullyFaithful.map_bijective`
  in `Mathlib.CategoryTheory.Functor.FullyFaithful` at lines 173–175.
  `Equivalence.mk` adjusts the unit, requiring no triangle identity on the input.
  This dependency's module is a proof-only `import` as required by stage 2.
- Supporting existing APIs: `CategoryTheory.Closed`, `MonoidalClosed`, `ihom`,
  `ihom.adjunction`, `ihom.ev`, `MonoidalClosed.curry`, `MonoidalClosed.pre`,
  and `MonoidalClosed.internalHom` in `Mathlib.CategoryTheory.Monoidal.Closed.Basic`.
  Read the complete signatures and docstrings. The upstream module
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic` supplies
  `ihomTensorToIhom` and its evaluation and invertibility results.
  `Mathlib.CategoryTheory.Monoidal.Braided.Basic` supplies `SymmetricCategory`.

Searches for duplicates (all performed before writing):

- `msearch.py ... leanfinder`:
  "In a closed symmetric monoidal category an invertible tensor factor gives internal
  Hom cancellation natural in both arguments and compatible with evaluation".
  Eight hits: evaluation/precomposition identities, rigid Hom-set bijections and
  `compTranspose`; no full statement.
- `msearch.py ... loogle`: `CategoryTheory.MonoidalClosed, CategoryTheory.ihom`.
  Twelve hits: internal-Hom functor projections, closed structures, and transport;
  no full statement.
- `msearch.py ... grep`:
  `ihom.*[Tt]ensor|[Tt]ensor.*[Ii]hom|[Cc]ancel` in `CategoryTheory/Monoidal`.
  Twenty-five capped hits, mostly unrelated cancellation tactics; no exact match.
- `msearch.py ... leansearch`:
  "Internal Hom cancellation of an invertible object from both arguments with natural
  evaluation compatible comparison". Eight hits: evaluation and unit internal-Hom
  isomorphisms, no simultaneous normalized cancellation.
- `msearch.py ... grep`: `curry.|ihomTensorToIhom|ihom.*[Cc]ancel`
  in `CategoryTheory/Monoidal/Closed`. Twenty-five hits: currying APIs, no exact match.
- Helper duplicate search, `msearch.py ... leanfinder`:
  "Simultaneous tensoring gives a canonical morphism from internal Hom X Y to internal
  Hom (X tensor J) (Y tensor J) in a symmetric closed monoidal category".
  Eight hits: `compTranspose`, `tensorClosed`, `comp`, `internalHomAdjunction₂`,
  `pre` and rigid Hom-set bijections; none gives this morphism.
- `msearch.py ... loogle`: `CategoryTheory.MonoidalClosed.ihomTensorBoth`.
  Zero hits (identifier unknown).
- `msearch.py ... grep`:
  `ihomTensorBoth|invertibleFactorHomCancellation|ihomTensorToIhom`
  in `CategoryTheory/Monoidal`. Zero Mathlib hits.
- Direct `rg` over the named upstream source, Mathlib and `lean/Sheaf`, and over
  `dag/lean_names_upstream.json`, checked the proposed names and concepts.
  Both proposed names were absent. Upstream `Rigid/Basic.lean:287` has the
  needed `ihomTensorToIhom`, which is reused. Its invertibility theorem proves only
  one part of this node. Upstream `Rigid/Braided.lean:192` has
  `ihomTensorObjWhiskerRightIso : [A ⊗ X,Z] ⊗ X ≅ [A,Z]`, a different comparison,
  requiring an exact pairing; it does not give this node's simultaneous transpose.
  The side snapshot has the corresponding declarations at shifted line numbers.
  `InvertibleDualizing.lean:258` supplies only the specialization with target the
  tensor unit. No general simultaneous map with the node's full properties was found.
- `grep -rn 'lem-sf-invertible-factor-hom-cancellation'` in the named upstream
  `WeilConjectures/` tree returned no matches. The side `lean/Sheaf` search likewise
  found no existing full statement.

Edge cases checked mathematically before writing:

- Tensor unit `J = I = 𝟙`: the canonical maps reduce to the standard unit comparisons.
- Arbitrary choices of `a,b`, including rescaling in one-dimensional vector spaces:
  neither definition depends on these choices; no hidden triangle hypothesis is needed.
- `X` need not be dualizable: the test-object argument uses invertibility of `J` alone.
  Arbitrary objects and arbitrary maps in each variable remain quantified.
- Zero source or target where present: equations are between the same zero morphisms;
  no nonzero or nonempty-object hypothesis is introduced.
- The zero category is included; the empty category cannot have a monoidal unit.
- `z = Iso.refl J`: factor compatibility reduces to identity compatibility.
  A nonidentity scalar isomorphism in vector spaces confirms the inverse belongs
  in the contravariant slot of the `s` equation.
- Independent universes `u,v` are retained. There are no site, index, coefficient,
  finite-dimensionality or smallness restrictions hidden in the formulation.

Validation: prescribed `scompile.py NF lem-sf-invertible-factor-hom-cancellation <file>`
compiled the sandbox and library module cleanly (1.1 s and 1.2 s). No errors or warnings.
Only the named main theorem has `sorry`; helper data are fully constructed.
The initial dry run identified a trailing `:=` in the recorded signature; the record was
corrected to the signature ending immediately before that delimiter.
All Lean lines are at most 100 characters; every universe and variable is explicitly bound.

## Second reading by NF

This is the author's final self-check; the dispatcher's brief assigns the independent
review to the maintainer and prohibits starting another agent. I reopened the node and
module and compared every hypothesis and clause as enumerated above. In particular I
checked all associator endpoints, that the two evaluation swaps cancel only using the
assumed symmetry, the direction of `pre f`, the `z.inv` in the source of the factor-change
map, and both inverse evaluation equations. No mismatch was found and no node statement
was changed. The existential isomorphism witnesses have prescribed hom maps, which also
makes the inverse maps unique; no hollow construction or arbitrary comparison is used.
