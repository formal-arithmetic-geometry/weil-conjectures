## Worker report

The module `Sheaf.CategoryTheory.TensorArrowMateRightUnit` states
`CategoryTheory.Adjunction.tensorArrowMate_right_unit`, with `sorry` as its only
proof. It formalizes both arbitrary-arrow right-action equations of
`lem-weil-pbc-tensor-arrow-mate-right-unit`. Only the node's `lean` field changes.
There are no new nodes, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- The categories C and D are `{C : Type u₁} [Category.{v₁} C]` and
  `{D : Type u₂} [Category.{v₂} D]`. All four universes are explicitly declared
  and independent; every other variable is explicitly bound in the theorem.
- The two tensor bifunctors are `(TC : C × C ⥤ C)` and `(TD : D × D ⥤ D)`.
  Product-category morphisms are made by Mathlib's `Prod.mkHom`. This is the
  literal uncurried bifunctor formulation of the node, including bifunctoriality.
- The specified functors and adjunction are `(L : C ⥤ D) (R : D ⥤ C)
  (adj : L ⊣ R)`. `Adjunction` includes the natural unit and counit and both
  triangle identities, even though this calculation only uses unit naturality.
- The natural comparison is `(mu : TC ⋙ L ≅ L.prod L ⋙ TD)`. Its component
  `mu.hom.app (M, P)` has precisely source `L.obj (TC.obj (M, P))` and target
  `TD.obj (L.obj M, L.obj P)`; naturality covers both arguments.
- The distinguished objects are `(oneC : C) (oneD : D)`.
  `rhoC : (𝟭 C).prod' ((Functor.const C).obj oneC) ⋙ TC ≅ 𝟭 C`
  and the corresponding `rhoD` encode the natural right-action isomorphisms.
  These are actual natural isomorphisms, not unrelated component isomorphisms.
- The given unit comparison is `(u : L.obj oneC ≅ oneD)`.
- The sole comparison coherence assumption is `right_action : ∀ M : C,
  mu.hom.app (M, oneC) ≫ TD.map (Prod.mkHom (𝟙 (L.obj M)) u.hom) ≫
  rhoD.hom.app (L.obj M) = L.map (rhoC.hom.app M)`.
  Lean writes composites in execution order, reversing the node's conventional
  right-to-left composition notation. This is exactly its displayed equation.
- The final binders `(K : C) (E : D) (c : L.obj K ⟶ E)` quantify over every
  object pair and every arrow c. No condition on c, such as invertibility or
  being a counit, is imposed.
- `F_K(P)`, `H_E(P)`, and `G_E(P)` in the node are auxiliary notation for
  `TC.obj (K, P)`, `TD.obj (E, L.obj P)`, and
  `R.obj (TD.obj (E, L.obj P))`. Their maps use `TC.map (Prod.mkHom (𝟙 K) f)`,
  `TD.map (Prod.mkHom (𝟙 E) (L.map f))`, and R of that last map. No extra
  independent structure or hypothesis is substituted for these functors.
- The node's beta at P is expanded as
  `mu.hom.app (K, P) ≫ TD.map (Prod.mkHom c (𝟙 (L.obj P)))`.
  Its alpha is `adj.unit.app (TC.obj (K, P)) ≫ R.map` of this beta.
  The node's `k_E` is expanded as
  `TD.map (Prod.mkHom (𝟙 E) u.hom) ≫ rhoD.hom.app E`.
  These are defining composites, with no choices or postponed data.
- The first conjunct is beta at `oneC` followed by k, equal to
  `L.map (rhoC.hom.app K) ≫ c`. Its hom set is
  `L.obj (TC.obj (K, oneC)) ⟶ E`.
- The second conjunct is alpha at `oneC` followed by `R.map` of k, equal to
  `rhoC.hom.app K ≫ adj.unit.app K ≫ R.map c`. Its hom set is
  `TC.obj (K, oneC) ⟶ R.obj E`.
- There is no monoidal-category, associator, left-unitor, shift, additive,
  exactness, or further coherence assumption. The two conclusions are joined
  by `∧`, matching both required equalities.

Dependency declaration used: the Mathlib leaf
`lem-weil-pbc-adjunction-of-natural-bijection` records
`CategoryTheory.Adjunction.mkOfHomEquiv` in
`Mathlib.CategoryTheory.Adjunction.Basic`. I read its full definition and
`Adjunction.CoreHomEquiv`, the `Adjunction` structure, and the related
`mkOfHomEquiv_homEquiv` signature. The consumer already assumes a specified
adjunction, so the theorem binds `adj : L ⊣ R` and uses its existing natural
unit `adj.unit`; it does not reconstruct a different adjunction or reprove
this dependency. Both statement/proof dependency lists consist of this same
Mathlib leaf, and its module is publicly imported. The other public import,
`Mathlib.CategoryTheory.Products.Basic`, supplies product categories,
`Functor.prod`, `Functor.prod'`, and `Prod.mkHom`.

Sources read: `literature/stacks-project/sites-cohomology.tex`,
`equation-projection-formula-map` (Tag 0B56), and the current blueprint file
`literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-thm-properbasechange/lemma-weil-pbc-perfect-projection-formula.proof.md`,
first paragraph, first sentence. The node is the agent-written categorical
expansion stated in its source record. The declaration's docstring carries
all three elementary proof steps, with unit naturality attributed to the
recorded adjunction node.

Edge cases checked before writing:

- Identity L and R with cartesian products and ordinary right actions: both
  equations reduce to naturality of the projection at any function c.
- Scaled right actions on rational vector spaces: take the identity adjunction,
  right actions scalar a and b, unit comparison scalar d, and tensor comparison
  scalar a/(bd), for nonzero a,b,d. Both sides of both equations are scalar
  a times c. Thus the statement preserves arbitrary right-action normalization
  and does not silently replace it by standard monoidal coherence.
- Rescaling the identity adjunction unit by nonzero t and its counit by 1/t
  multiplies both sides of the second identity by t, as required.
- Zero arrows and zero objects, when present, satisfy the two formulas without
  a nonzero hypothesis. No zero structure is required on a general category.
- The binders oneC and oneD already require objects, exactly as the node does;
  no additional nonemptiness or inhabitedness hypothesis excludes a case.
- Product-category universes are maxima of the two factors, not an imposed
  equality between the object and morphism universes.

Searches (all through the prescribed `msearch.py` wrapper, group NF and this
item, except direct project-source ripgrep):

1. `leanfinder`: "Adjunction tensor bifunctor right unit normalization arbitrary
   arrow mate without monoidal associator". Eight hits included
   `Adjunction.unit_app_tensor_comp_map_δ`, its `_assoc` variant,
   `Adjunction.rightAdjointLaxMonoidal_μ`, and dual-object `rightAdjointMate`
   statements. All concern full monoidal structures or rigid duals, rather
   than these bare-bifunctor arbitrary-arrow equations.
2. `loogle`: `"rightUnitor", "unit"`. Twelve hits concerned the unitors for
   functor composition and products of categories; none was this statement.
3. `grep`: `unit_app_tensor_comp_map_δ|rightAdjointLaxMonoidal_μ` in
   `CategoryTheory`. Six hits in Mathlib's monoidal functor and transformation
   modules. I read `Monoidal/Functor.lean` at the candidate statement and its
   assumptions: monoidal categories, oplax/lax structures and a monoidal
   adjunction are required, unlike this node.
4. `leansearch`: "For tensor bifunctors with natural right unit isomorphisms,
   evaluating the adjunct of c tensor identity at the unit equals the adjunct
   of c followed by the right unit isomorphism". Eight hits included
   `Functor.LaxMonoidal.ofBifunctor.topMapᵣ`,
   `Adjunction.unit_app_unit_comp_map_η`, `MonoidalCategory.rightUnitorNatIso`,
   and `conjugateEquiv_rightUnitor_hom`. These use different unitors or extra
   monoidal structure and do not state the two equalities.
5. Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
   `tensorArrowMate|tensor_arrow_mate|rightUnit.*[Mm]ate|mate.*[Rr]ightUnit`:
   only unrelated functor-composition mate unitors appeared. The required
   upstream `grep -rn` for the exact node id returned no match.
6. Broader project searches for tensor mates and projection-map unitors led to
   `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`; I read its
   bare-bifunctor right-adjoint projection-map interface and signatures.
   Those specialize c to a counit and do not state either arbitrary-arrow
   right-action conclusion. No duplicate was found.
7. The proposed name `tensorArrowMate_right_unit` was searched in Mathlib,
   upstream, Sheaf and `dag/lean_names_upstream.json`: no collision.

Compilation: prescribed `scompile.py NF <item> <module>` passed for both the
sandbox and actual library module, with no warnings or errors. The initial
attempt exposed pair-constructor inference at product-category arrows;
replacing ordinary pairs of arrows with Mathlib's documented `Prod.mkHom`
fixed this without changing the statement. No global build was run.

No statement dispute or node fault was found.

## Second reading by NF

This dispatcher assigned a single worker and explicitly forbids starting other
agents. This is a separate rereading by the same worker; the maintainer's
independent reading remains part of delivery review.

I reopened the node and final Lean file. In `mu` the comparison points from
L of tensor to tensor of L, not its inverse. Both `rhoC` and `rhoD` point from
tensor on the right by the distinguished object to the original object.
The first equation has exactly beta followed by `k_E`, while the second has
unit, then R of beta, then R of `k_E`; its right side begins with `rhoC` and
ends with R of c. I checked source and target at each composition against the
two hom sets printed in the node. The universal right-action hypothesis is
present at every M, and c remains arbitrary. No naturality, invertibility or
triangle-identity data were dropped: they are carried by the functors,
natural isomorphisms and the specified `Adjunction`. No extra coherence was
introduced. The docstring contains all three proof steps and the only proof
is `sorry`. No changes were needed in this second pass.
