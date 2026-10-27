## Worker report

The module `Sheaf.Algebra.Homology.ResolvingClassDerivedDescent` states
`CategoryTheory.BoundedResolvingDescent.resolvingClassDerivedDescent`, with one
`sorry`. Seven auxiliary definitions give the subcategories, inclusions and arrow
classes introduced in this very node. They have concrete data, no postponed proofs,
and are all listed in `lean.declarations`. No existing node field except `lean`
changes. No dependency repair, statement correction or new DAG node is needed.

I read the item, all three statement dependencies and their recorded declarations,
and all ten proof dependencies. Sources read include Stacks `derived.tex`, Tag
0794's first proof paragraph and Tag 0GSL, as well as the recorded proof of Tag
05T7(1) in `SubcategoryLeftResolution.lean`. The current blueprint unit and chapter
were read through `literature/blueprint/latest/`; this generic supporting lemma
does not change their statements or route. No repair note for this item was found.

Hypotheses and the definitions of the objects match as follows:

| Node | Lean |
| --- | --- |
| Abelian categories A and B | `A : Type uA`, `[Category.{vA} A]`, `[Abelian A]`, and the corresponding independent binders for B. |
| Integer cochain and homotopy categories | `CochainComplex A ℤ` and `HomotopyCategory A (ComplexShape.up ℤ)`. |
| Derived localizations in the chosen larger universe | `[HasDerivedCategory.{w} A]`, `[HasDerivedCategory.{w} B]`, and `DerivedCategory.Qh`. Object and original morphism universes of A and B remain independent. |
| P contains zero | `(P : ObjectProperty A)` and `[P.ContainsZero]`; together with iso closure this contains the chosen zero and every zero object. |
| P is closed under isomorphisms | `[P.IsClosedUnderIsomorphisms]`. |
| P is closed under finite biproducts | `[P.IsClosedUnderFiniteCoproducts]`. In an abelian category finite coproducts are finite biproducts, including the empty one. |
| Every object is an epimorphic image from P | `hcover : ∀ X, ∃ (Y : A) (p : Y ⟶ X), P Y ∧ Epi p`. |
| C consists of complexes with bounded above cohomology | `(homotopyProperty A).FullSubcategory`, where `homotopyProperty` is the inverse image of `DerivedCategory.TStructure.t.minus` under Qh. |
| R is the full subcategory of strictly bounded above P-term complexes in C | `(resolvingProperty A P).FullSubcategory`; its property is `complexProperty A P M.obj.as`, meaning `(∃ b, M.obj.as.IsStrictlyLE b) ∧ ∀ j, P (M.obj.as.X j)`. |
| Restricted quasi-isomorphisms W_C and W_R | `quasiIsoC` and `quasiIsoR`, defined using `HomotopyCategory.quasiIso` and `MorphismProperty.inverseImage` along the actual inclusions. |
| D minus | Mathlib's existing `DerivedCategory.Minus A`. |
| Localizations of C and R | Arbitrary `LC`, `LR`, `qC`, `qR` with their `IsLocalization` instances. These merely spell out the localizations denoted in the node; no calculus is assumed for them. |

The inverse-image presentation of C is exact, not a restriction to complexes that
are strictly bounded above. `TStructure.minus` is `∃ n, IsLE _ n`;
`DerivedCategory.isLE_iff` identifies this with cohomology vanishing above n.
`HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh` compares cohomology
after Qh with homotopy cohomology, and
`HomotopyCategory.homologyFunctorFactors` compares it with the complex's
cohomology. Homotopy-category objects retain their actual complex as `.as`.
Thus every acyclic, possibly unbounded complex belongs to C. The definition
`toMinus` is the literal `ObjectProperty.lift` of the inclusion followed by Qh,
using the membership proof already carried by the object. It uses no choice of
resolution and no auxiliary theorem.

Every conclusion is present in the single conjunction:

1. `(quasiIsoC A).HasRightCalculusOfFractions` is the calculus for W_C.
2. `(quasiIsoR A P).HasRightCalculusOfFractions` is the calculus for W_R.
3. The existential `J : LC ⥤ DerivedCategory A` has `J.Full`, `J.Faithful`,
   the inclusion comparison `qC ⋙ J ≅ (homotopyProperty A).ι ⋙ Qh`, and
   `J.essImage = TStructure.t.minus`. The equality specifies exactly D minus,
   rather than just containment or essential surjectivity onto all D(A).
4. The existential `I : LR ⥤ LC` has `I.IsEquivalence` and the inclusion
   comparison `qR ⋙ I ≅ (resolvingProperty A P).ι ⋙ qC`.
5. For every complex M and every integer b, vanishing `IsZero (M.homology j)`
   for j > b implies existence of `V`, `v : V ⟶ M`, `QuasiIso v`, all terms
   in P, and `IsZero (V.X j)` for j > b. The same supplied b occurs on both
   sides; no degreewise epimorphism onto the original unbounded M is asserted.
6. For every additive `F : A ⥤ B`, the stated implication assumes only that
   termwise F preserves quasi-isomorphisms between `complexProperty A P`
   complexes. Its conclusion gives `Fhat : DerivedCategory.Minus A ⥤
   DerivedCategory B` and a natural isomorphism
   `(resolvingProperty A P).ι ⋙ toMinus A ⋙ Fhat ≅
   inclusion A P ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh`.

For the last clause, take an object M of R and evaluate this natural isomorphism:
its source is Fhat(Q_A M) and its target is Q_B(K(F)M), exactly rho_M in the
node. Given a chain map f between such complexes, apply the quotient functor
and wrap its morphism twice with `ObjectProperty.homMk`. Naturality reads
`Fhat.map (Q_A.map f) ≫ rho_N.hom = rho_M.hom ≫ Q_B.map (K(F).map f)`.
This is precisely the node's displayed equation in Lean's left-to-right
composition convention. `Functor.mapHomotopyCategory_map` identifies the
right-hand map with termwise F(f). If Q is used directly from chain complexes,
the existing `DerivedCategory.quotientCompQhIso` supplies the canonical
comparison, natural for every chain map. Naturality on the full homotopy
subcategory is equivalent to naturality for every chain map, since the
quotient functor is full. It adds no restriction on resolutions. The theorem
assumes no exactness, colimits, enough projectives, or functorial covers.

Dependency declarations used, with source signatures and docstrings read:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`,
  `DerivedCategory.quotientCompQhIso`, and their localization instances.
- `Mathlib.CategoryTheory.Localization.Predicate`: `Localization.lift`,
  `Localization.fac`, `Localization.Lifting`, `Localization.liftNatTrans`,
  `Localization.liftNatTrans_app`, `Localization.liftNatTrans_id`,
  `Localization.comp_liftNatTrans`, `Localization.liftNatIso`,
  `Localization.natTrans_ext`, `Localization.fullyFaithfulWhiskeringLeft`, and
  `Localization.essSurj`. The localization and natural comparisons in the
  conclusion use this same universal-property notion.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `TStructure.t`,
  `isLE_iff`, `Minus`, `Minus.ι`.
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`: the left and right
  calculus instances for `HomotopyCategory.quasiIso`.
- `Mathlib.CategoryTheory.Localization.CalculusOfFractions`:
  `Localization.exists_rightFraction`,
  `MorphismProperty.RightFraction.map_eq_iff` and `RightFractionRel`.
- `Mathlib.CategoryTheory.Equivalence`: `Functor.IsEquivalence`,
  `Functor.asEquivalence`.
- `Sheaf.Algebra.Homology.SubcategoryLeftResolution`:
  `CochainComplex.exists_subcategory_left_resolution`.
- `Sheaf.CategoryTheory.RightFractionDenseSubcategory`:
  `CategoryTheory.rightFractionDenseSubcategory`.
- `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`: the additive
  `mapHomotopyCategory` triangulated instance named by
  `lem-trf-additive-homotopy-triangulated`. Its underlying termwise functor is
  `Functor.mapHomotopyCategory` in `Mathlib.Algebra.Homology.HomotopyCategory`.

The direct proof imports retain every recorded proof dependency. The theorem's
docstring contains all nine proof steps, including the common-refinement
faithfulness argument and the construction and naturality of rho.

Edge cases checked mathematically before writing: the zero abelian category;
P equal to all objects; acyclic complexes unbounded in their terms; zero complexes;
arbitrary negative, zero and positive b; empty finite biproducts. The same-bound
resolution uses good truncation before the existing strict-resolution lemma,
so does not falsely assert a degreewise epimorphism onto M above b. An additive
non-exact example is tensor with Z/2 on abelian groups with P the free groups:
the statement asks only for preservation on bounded above free complexes, not
global preservation of homology. Arbitrary universes of A, B and the two chosen
localization presentations are retained. No disputed statement was found.

Searches actually run via `msearch.py` with this group and item:

- LeanFinder: “An additive functor preserving quasi-isomorphisms between bounded
  above complexes in an epimorphically generating class descends to the bounded
  above derived category”. Eight hits concerned `mapDerivedCategory`, its
  comparisons, and `mapHomologicalComplexUpToQuasiIso`; their source hypotheses
  demand global exactness or preservation of homology, so none is this theorem.
- Loogle: `"HasLeftResolutions", "Localization"`. Zero hits.
- Mathlib grep: `HasLeftResolutions|isLeftDerivabilityStructure|mapHomologicalComplexUpToQuasiIsoFactors`.
  Twenty-five hits. The generic derivability constructor requires supplied
  resolution data; it does not state the same-bound resolution and descent here.
- Mathlib grep: `Resolving|resolving|isBoundedAbove|IsBoundedAbove` under
  `Algebra/Homology`, and `namespace Minus|def IsMinus|abbrev Minus|HasRightCalculusOfFractions|def lift`
  under `Algebra/Homology/DerivedCategory`; these located the existing bounded
  derived category and ambient calculus, which are reused.
- Project `rg` searches for resolving/bounded notions in `lean/Sheaf`,
  `lean/WeilConjectures`, and their homological-algebra directories found the
  existing `LeftDerivedFromResolvingClass` theorem, which assumes unbounded
  resolving covers for every homotopy object and a triangulated functor. Its
  signature was read; it does not state this theorem. Searches for the exact
  item id, `resolvingClassDerivedDescent`, `BoundedResolvingDescent`, and
  `cohomologicallyBoundedAbove` found no duplicate declaration of this item.

Server validation: the first `scompile.py` compiled both its sandbox probe and
the actual module cleanly (1.6 s and 1.8 s). Direct imports of the statement
and proof dependency modules were then made explicit before final validation.

## Second reading by Q52

This is a self-audit with the node and module reopened, not a claim of an
independent worker review. The dispatcher explicitly forbids starting another
agent; the maintainer supplies the independent review after delivery.

I checked each hypothesis and all six conclusion groups above against the
literal theorem. In particular, C is cohomologically bounded, whereas R is
strictly bounded; W_R is restricted along the composite inclusion, not a class
of arbitrary maps; the J comparison identifies the intended induced functor;
its essential image is an equality; the I comparison identifies the intended
inclusion equivalence; the resolution retains the exact integer b. The F
assumption quantifies over every chain map between all strict P-term complexes,
and the conclusion is one natural isomorphism, not unrelated objectwise choices.
This yields exactly the naturality equation with no extra triangulated or exact
functor hypothesis. All seven helper definitions are explicit constructions of
objects already introduced by the node. The only revision after the initial
compile was to make the recorded dependency imports explicit. There is no
statement mismatch or statement correction.
