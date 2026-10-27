## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.ResolvingRoofAmbientCompatibility`
states `DerivedCategory.exists_resolving_roof_ambient_compatibility`, with `sorry` as
its entire proof. The auxiliary definition `DerivedCategory.resolvingRoofQMinus`
is the canonical restriction of `DerivedCategory.Q` to bounded above complexes
with values in the bounded above derived category. It has real data: objects
are `Q.obj M.obj` and arrows are `Q.map f.hom`. Its proof of membership uses an
upper bound already certified by `M.property`; the chosen integer affects only
a proof, never the underlying object or morphism. It introduces no replacement
for complexes, boundedness, localization, or the derived category.

Sources read: `literature/stacks-project/derived.tex`,
`proposition-left-derived-exists` (Tag 0794), from its assumptions through the
common-roof diagram and cohomology square; and
`lemma-subcategory-left-resolution` (Tag 05T7), especially clause (2).
The common-refinement interface is Mathlib's formalization of Categories Tags
04VI/04VJ. The current blueprint unit `literature/blueprint/latest/blueprint/
sec-trace-formula/sk-i-curve-zero/_section.md` was also read: this item is an
auxiliary node, not that unit's own statement. No statement correction is needed.

Hypotheses and clauses, in node order:

- Abelian categories are `A : Type u₁`, `[Category.{v₁} A]`, `[Abelian A]`,
  and independently `B : Type u₂`, `[Category.{v₂} B]`, `[Abelian B]`.
  `[HasDerivedCategory.{w} A]` and `[HasDerivedCategory.{w} B]` put both
  localizations in the common morphism universe `w`. All five universes are
  explicit; object and morphism universes of A and B are not equated.
- The class is `P : ObjectProperty A`. `[P.ContainsZero]` and
  `[P.IsClosedUnderIsomorphisms]` express the first two assumptions. `h_sum`
  expresses binary biproduct closure, which together with zero and iso-closure
  is exactly closure under all finite biproducts. `h_epi` supplies, for each
  `X`, an object `T` in P and an epimorphism `e : T ⟶ X`. There is no assumption
  that P consists of projectives or is closed under summands.
- `E G : CochainComplex.Minus A` are actual integer-indexed complexes with an
  existential strict upper bound, using the existing upstream
  `CochainComplex.minus`. The term conditions are exactly `hE` and `hG`.
  Thus these are representatives of the node's objects of R. Their maps in
  the statement are chain maps; homotopy-category equality is expressed by
  `Nonempty (Homotopy ...)`, without choosing maps on homotopy classes.
- `DerivedCategory.Minus A` is Mathlib's full subcategory for the canonical
  t-structure. `TStructure.minus` means `∃ n, t.IsLE X n`, and
  `DerivedCategory.isLE_iff` identifies this with vanishing of cohomology
  above n. The helper `resolvingRoofQMinus` just certifies membership of
  localized bounded above complexes in that existing full subcategory.
- `Y : CochainComplex A ℤ` has no bound, term-class membership, or exactness
  assumption. `b : E.obj ⟶ Y` and `c : G.obj ⟶ Y` are the specified chain maps.
- `a : Q.obj E.obj ≅ Q.obj G.obj` is the given derived isomorphism.
  `ha : a.hom ≫ Q.map c = Q.map b` is precisely `Q(c) a = Q(b)`.
- The existential `L : CochainComplex.Minus A`, followed by its term
  condition, says L belongs to R. `p : L.obj ⟶ E.obj`, `q : L.obj ⟶ G.obj`
  and `QuasiIso p ∧ QuasiIso q` are exactly the two required roof maps.
- `Q.map p ≫ a.hom = Q.map q` is the node's roof formula in cancellation
  form: since p is a quasi-isomorphism, `Q.map p` is invertible, and this
  equation is equivalent to `a.hom = inv (Q.map p) ≫ Q.map q`.
  This avoids an artificial extra invertibility assumption or typeclass binder.
- `Nonempty (Homotopy (q ≫ c) (p ≫ b))` is exactly the specified chain
  homotopy. Mathlib's `Homotopy.hom i j` is zero unless `j + 1 = i`;
  its `comm` equation is `f.f i = dNext i hom + prevD i hom + g.f i`.
  Specializing to cochains, subtracting `g.f i`, and setting
  `h^i = hom i (i-1)` gives precisely
  `(cq-bp)^i = h^i ≫ d_Y^(i-1) + d_L^i ≫ h^(i+1)`, i.e. the node's
  displayed equation in Lean's left-to-right composition order.
- The conclusion universally quantifies over `F : A ⥤ B`, `[F.Additive]`.
  Its preservation premise ranges only over `M N : CochainComplex.Minus A`
  whose terms belong to P, and only requires that termwise F sends a
  quasi-isomorphism between them to a quasi-isomorphism. The action on
  complexes and maps is the existing `F.mapHomologicalComplex (.up ℤ)`.
- `S : DerivedCategory.Minus A ⥤ DerivedCategory B` is arbitrary.
  `ρ M hM` is an actual isomorphism from `S(Q M)` to `Q(F M)` for every
  bounded above P-complex M. The extra argument `hM` is a proof of membership,
  hence proof-irrelevant; no additional datum is imposed.
- The naturality premise quantifies over every such M,N and every chain map f.
  Its equation is `S(Q f) ≫ (ρ N hN).hom = (ρ M hM).hom ≫ Q(F f)`.
  `ObjectProperty.homMk` supplies the same map in the relevant full subcategory.
- The expression `(ρ E hE).inv ≫ S.map (ObjectProperty.homMk a.hom) ≫
  (ρ G hG).hom` is exactly the hom of the node's Θ. It is an isomorphism:
  both ρ components are isomorphisms, the lift of a through a full subcategory
  is an isomorphism, and every functor preserves isomorphisms.
  The final two equalities are `Q(F p) ≫ Θ = Q(F q)` and
  `Θ ≫ Q(F c) = Q(F b)`, with composition written in Lean order.
- The quantifiers for F,S,ρ occur after the existential roof: the same roof
  works for every specified S and ρ, including noncanonical choices satisfying
  the stated naturality. No existence or universal property for S is assumed.

Dependency interfaces read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, the recorded Mathlib match.
- `def-weil-abstract-derived-category`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, the recorded declarations.
- These are exposed by the public import
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`, which also gives
  `DerivedCategory.Minus` and its cohomological characterization.
- Upstream `WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus`:
  `CochainComplex.minus` and `CochainComplex.Minus`; the recorded source was
  opened in full, including its definition of strict upper boundedness.
- `Mathlib.CategoryTheory.ObjectProperty.ContainsZero`: P contains a zero object;
  Mathlib `ObjectProperty.IsClosedUnderIsomorphisms` gives iso-closure.
- Already-stated proof dependencies are available through the public t-structure
  import: both calculus-of-fractions instances in
  `Mathlib.Algebra.Homology.DerivedCategory.Fractions`, and
  `CategoryTheory.Localization.exists_rightFraction` and
  `CategoryTheory.MorphismProperty.RightFraction.map_eq_iff` in
  `Mathlib.CategoryTheory.Localization.CalculusOfFractions`. Their signatures
  and the right-fraction proof were opened. No redundant proof-only import is
  needed. `lem-trf-resolving-class-derived-descent` currently has no recorded
  Lean statement, so it has no module to import; only its resolution clause
  is used in the natural-language proof plan, not to type this statement.

Searches (2026-10-24, output also recorded by msearch in searches.jsonl):

- LeanFinder: “A derived isomorphism between bounded above resolving class
  complexes has a common resolving roof compatible up to chain homotopy with
  maps to an arbitrary target.” Eight hits: `DerivedCategory.right_fac`,
  LeftResolution and injective/projective-resolution comparisons. None imposes
  an arbitrary quotient-generating term class together with the ambient-target
  homotopy and the arbitrary specified S,ρ compatibilities.
- LeanSearch: “A derived isomorphism between bounded above complexes has a
  common roof in an epimorphism generating class compatible with a homotopy to
  any target.” Eight hits, mostly short-complex homology and general localization
  functoriality. No exact statement.
- Loogle: `DerivedCategory.right_fac, Homotopy, ObjectProperty` returned no hits
  (ObjectProperty unknown to that service). Retried with
  `"DerivedCategory.right_fac"`: three valid hits, the unbounded right-fraction
  result and its strict-bound variants. None is the present statement.
- msearch grep in Mathlib `Algebra/Homology/DerivedCategory`:
  `resolving|right_fac_of_isStrictlyLE` returned six hits, all fraction variants
  or uses. `QMinus|toMinus|resolvingRoof|resolving_roof` in `Algebra/Homology`
  returned no hits. Local source searches for bounded-above localization lifts
  found only filtration-specific constructions and the existing Minus category.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for resolving classes and
  `resolvingRoofQMinus|exists_resolving_roof_ambient_compatibility|resolving.roof|
  ambient.compatib` found no duplicate. Existing resolving-class derived-functor
  and natural-transformation APIs have different hypotheses and conclusions.
  `grep -rn` of the item id in `lean/WeilConjectures` returned no declaration.
  Both new full names were also searched in `dag/lean_names_upstream.json`.
  DAG searches for `CochainComplex.Minus`, `CochainComplex.minus`, and
  `DerivedCategory.Minus` confirm existing bounded-category interfaces; none
  records this canonical restricted localization or this theorem.

Edge cases checked mathematically: zero complexes and the class containing
only zero in the zero category satisfy the formulation; an empty class is
excluded exactly by containing zero and quotient generation. Upper bounds
are existential integers, not natural numbers or one common chosen bound,
so negative bounds and different bounds for E,G,L are included. A completely
unbounded Y remains admissible. No term condition on Y or F(Y) occurs. The
identity additive functor, and arbitrary natural automorphisms of comparison
data, remain admissible. Neither exactness of F nor colimits, functorial
resolutions, projectivity, or preservation on all quasi-isomorphisms is added.

Validation: scompile.py compiled the file in sandbox mode and at its actual
library module path, both cleanly (11.3 s and 2.1 s reported). All variables and
universes are bound explicitly; all lines have at most 100 characters. The only
postponed theorem is the item's theorem. No new nodes, dependency modules,
statement changes, or unresolved statement disputes.

## Second reading by Q62

A separate pass through the final file against the node and the above source
paragraphs checked every clause. This is the dispatcher's single worker's
second pass; no independent worker or sub-agent review is claimed. The delivery
is for the maintainer's independent review, as required by the brief.

In particular, the check verified that the common larger universe is shared
only by the derived hom sizes; the two underlying categories retain independent
sizes. The helper's upper-bound proof wraps the same Q object and map without
choosing a resolution. Binary sum closure plus zero covers the empty finite
sum. The same existential roof precedes all of F,S,ρ, and the preservation
premise includes only R. S receives the full-subcategory lift of the given a,
not an independently chosen comparison. The roof equation was checked in
cancellation form using the explicitly asserted quasi-isomorphism p. The
homotopy argument order is `(q ≫ c)` to `(p ≫ b)`, matching the displayed
subtraction. Both final equations were read with Lean's composition order.
No mathematical mismatch was found. During elaboration, the dependent ρ
membership argument was made an explicit binder and the source/target of
the lifted a were made explicit; these changes only resolve parsing and
full-subcategory inference, and add no mathematical hypotheses.
