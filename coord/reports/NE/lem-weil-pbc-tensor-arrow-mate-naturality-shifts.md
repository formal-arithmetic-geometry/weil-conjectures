## Worker report

The module `Sheaf.CategoryTheory.TensorArrowMateNaturalityShifts` states
`CategoryTheory.TensorArrowMate.naturality_shifts`, with its entire proof `sorry`.
Its two owning-node helpers `beta` and `alpha` have real data: beta is the comparison
followed by the tensor image of c, and alpha is exactly its adjunct for `adj`.
All three declarations are listed in `lean.declarations`. No independent notion,
new node, dependency repair, or statement correction is needed. Only the item's
`lean` record changes.

Source read: `literature/stacks-project/sites-cohomology.tex`, section Projection
formula, equation-projection-formula-map (Tag 0B56). That source defines the
counit case; the arbitrary-arrow naturality and shifts are the seven agent-written
steps of this node, all included in the theorem docstring. The upstream
`Adjunction/ProjectionMap.lean`, `ProjectionMapCompat.lean`, and
`ProjectionMapShift.lean` concern counit projection maps and do not already state
this arbitrary-arrow result.

The hypothesis and conclusion correspondence is as follows. Lean writes `f ≫ g`
for g after f, reversing the displayed functional-order composites of the node.

| Node component | Lean rendering |
| --- | --- |
| Categories C,D, with no restrictions on sizes | Explicit `C : Type u₁`, `D : Type u₂`, `Category.{v₁} C`, `Category.{v₂} D`; all four universes are bound independently. |
| Arbitrary bifunctors on C and D | `TC : C ⥤ C ⥤ C`, `TD : D ⥤ D ⥤ D`. Currying supplies exactly the same data and naturality as functors from the product category. |
| L, R and specified adjunction, natural unit/counit, triangle identities | `L : C ⥤ D`, `R : D ⥤ C`, `adj : L ⊣ R`; Mathlib `Adjunction` stores the natural unit/counit and both triangle identities. |
| Natural tensor comparison μ in both inputs | The natural isomorphism `μ` between `TC ⋙ (Functor.whiskeringRight C C D).obj L` and `(L ⋙ TD) ⋙ (Functor.whiskeringLeft C D D).obj L`; its component at K, then P, is μ(K,P). |
| F_K, H_E, G_E | Respectively `TC.obj K`, `L ⋙ TD.obj E`, and `(L ⋙ TD.obj E) ⋙ R`. These are existing functor compositions, without additional definitions. |
| βᶜ_P | `beta TC TD L μ c P`, definitionally `(μ.hom.app K).app P ≫ (TD.map c).app (L.obj P)`. |
| αᶜ_P | `alpha TC TD L R adj μ c P`, defined by `adj.homEquiv _ _ (beta ... c P)`; `Adjunction.homEquiv` definitionally expands to `adj.unit.app _ ≫ R.map (beta ... c P)`. |
| Coherent integer shifts, all auto-equivalences | `HasShift C ℤ`, `HasShift D ℤ`. An action by the group ℤ makes each shift invertible via its negative shift. |
| Coherent comparisons l,r,t for L,R and every fixed tensor input | `L.CommShift ℤ`, `R.CommShift ℤ`, and the two families `∀ M, (TC.obj M).CommShift ℤ`, `∀ M, (TD.obj M).CommShift ℤ`. |
| Tensor comparisons natural in the fixed input M | `hTC` and `hTD` assert `NatTrans.CommShift (TC.map f) ℤ` and its TD counterpart for every morphism f. This is precisely the comparison naturality square in M. |
| η commutes with induced comparison on RL | `hη : NatTrans.CommShift adj.unit ℤ`. The identity functor's comparison is identity on components; the composite comparison is L(l) followed by r as specified. |
| μ(K,-) commutes with composite comparisons for every K,n | `hμ : ∀ K, NatTrans.CommShift ... (μ.hom.app K) ℤ`, with source `TC.obj K ⋙ L` and target `L ⋙ TD.obj (L.obj K)` explicitly supplied for instance inference. |
| a(n,P) | `((TC.obj K ⋙ L).commShiftIso n).hom.app P`, equal by Mathlib's composite formula to `L.map (t^K) ≫ l`. |
| b(n,P) | `((L ⋙ TD.obj (L.obj K)).commShiftIso n).hom.app P`, equal to `T_LK.map l ≫ t^(LK)` in hμ. |
| h(n,P) | `((L ⋙ TD.obj E).commShiftIso n).hom.app P`, equal to `T_E.map l ≫ t^E`. |
| g(n,P) | `(((L ⋙ TD.obj E) ⋙ R).commShiftIso n).hom.app P`, equal to `R.map h ≫ r`. |
| First shift equation, all K,E,c,P,n | First conjunct inside the first universal quantifier: `beta ... (P⟦n⟧) ≫ h = a ≫ (beta ... P)⟦n⟧'`. |
| Second shift equation, same quantifiers | Second conjunct: `alpha ... (P⟦n⟧) ≫ g = t^K ≫ (alpha ... P)⟦n⟧'`. |
| K',E',c',a,b and commuting square | The second outer conjunct universally binds these objects and maps, then assumes `c ≫ b = L.map a ≫ c'`. |
| All p:P→P' | `∀ (P P' : C) (p : P ⟶ P')` in the naturality conjunct. |
| b ⊗ Lp | `(TD.map b).app (L.obj P) ≫ (TD.obj E').map (L.map p)`. |
| a ⊗ p | `(TC.map a).app P ≫ (TC.obj K').map p`. |
| Naturality of β | First inner conjunct: `beta ... c P ≫ (b ⊗ Lp) = L.map (a ⊗ p) ≫ beta ... c' P'`. |
| Naturality of α | Second inner conjunct: `alpha ... c P ≫ R.map (b ⊗ Lp) = (a ⊗ p) ≫ alpha ... c' P'`. |
| No exactness, tensor associator, unit, invertibility assumptions | None of these structures or hypotheses occurs in the signature. |

Dependency declarations read and used:

- `lem-weil-pbc-adjunction-of-natural-bijection` is a Mathlib leaf recorded on
  `CategoryTheory.Adjunction.mkOfHomEquiv` in `Mathlib.CategoryTheory.Adjunction.Basic`.
  Read `CoreHomEquiv`, `mkOfHomEquiv`, `mkOfHomEquiv_homEquiv`, `homEquiv`, and
  `homEquiv_unit` with their docstrings. The item begins with a specified adjunction,
  so it uses `Adjunction` and its actual `homEquiv`, rather than constructing another.
- `lem-weil-pbc-commshift-nattrans-comp-whisker` is a Mathlib leaf recorded on
  `CategoryTheory.NatTrans.CommShift.comp` in `Mathlib.CategoryTheory.Shift.CommShift`.
  Read `Functor.CommShift.comp`, `commShiftIso_comp_hom_app`, `NatTrans.CommShift`,
  `NatTrans.shift_app_comm`, and the id/comp/whiskerLeft/whiskerRight/associator
  instances. These give exactly the composite convention and all-integer equations.
- `Mathlib.CategoryTheory.Whiskering`: `Functor.whiskeringLeft` and
  `Functor.whiskeringRight` give the fully natural curried tensor comparison.
- `Mathlib.Algebra.Group.Int.Defs` supplies the integer additive-group instances.

Edge cases checked by reading the equations and their domains/codomains:

- n=0 and n negative are included by the unrestricted integer quantifier and the
  coherent comparisons; there is no positive-shift restriction.
- Identity adjunction with identity μ reduces beta and alpha to `c ⊗ 1`; the shift
  equation becomes exactly hTD applied to c.
- Identity a,b,p recovers ordinary naturality in P; arbitrary noninvertible c and
  noninvertible a,b,p remain allowed. If a zero map exists, c=0 is also allowed;
  no preadditivity or zero object is imposed.
- Empty categories cause only the expected empty object quantifiers. There are no
  chosen objects or Nonempty assumptions, and no tensor unit needs to exist.
- All four universes are independent; neither category is required to be small or
  locally small in the other category's universe.

Searches performed before writing:

- `msearch.py ... leanfinder`: query "Adjunct of a tensor comparison followed by
  arbitrary arrow is natural in commuting squares and compatible with integer
  shifts"; 8 hits, including `Adjunction.CommShift` and shift comparison lemmas;
  none states the arbitrary-arrow tensor result.
- `msearch.py ... loogle`: query
  `CategoryTheory.NatTrans.CommShift, CategoryTheory.Adjunction.homEquiv`; 0 hits.
- `msearch.py ... grep`: query
  `tensor.*[Mm]ate|[Mm]ate.*tensor|rightAdjoint.*[Pp]rojection` in CategoryTheory;
  6 hits in rigid monoidal categories, with additional structure and no match.
- `msearch.py ... leansearch`: query "The adjunct of an arbitrary tensor
  comparison arrow is natural in commuting squares and commutes with integer
  shifts"; 8 hits on generic adjunction comparisons and `CommShiftCore`, no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `tensorArrow|TensorArrow|tensor.*[Mm]ate|[Mm]ate.*tensor`: specialized projection,
  scalar and geometric mate declarations; inspected the projection modules and the
  related `FormalExactProjectionMate` and `TensorParameterComposition`. The former
  fixes c to the counit and assumes exactness/right units; the latter states a
  different parameter composition equation. Neither is this statement.
- Searched the exact node id under `lean/WeilConjectures`: no hit.
- Searched `namespace TensorArrowMate|tensorArrowMate_naturality_shifts` in both
  library roots and `dag/lean_names_upstream.json`: no hit.

Validation: `scompile.py NE lem-weil-pbc-tensor-arrow-mate-naturality-shifts <file>`
compiled both the isolated sandbox module (7.3 s) and its actual library module
(3.6 s), exit 0, no errors or warnings. Initial compilation identified missing
Whiskering/integer-instance imports and an instance-inference problem through the
curried functor; imports and the explicit F₁/F₂ in hμ fixed those without changing
mathematical hypotheses. No #check lines or local notation remain.

No STATEMENT-DISPUTED flag or node fault.

## Second reading by NE

A separate second pass by this worker reopened the node and the completed module.
The dispatcher explicitly forbids starting other agents, so this is not claimed
as an independent worker review; the maintainer's independent review remains due.

Checked each row of the correspondence above against the TeX. The direction of μ
is L(K⊗P) to LK⊗LP; beta uses its hom, not its inverse. Alpha uses the given
adjunction rather than a chosen bijection. Expanded Mathlib's composite comparison
formula to verify a,b,h,g in the order `L.map(t) ≫ l`, `T.map(l) ≫ t`, and
`R.map(h) ≫ r`. Expanded `NatTrans.shift_app_comm` to verify the orientations of
hη and hμ: after reversing the node's functional-order notation, they are exactly
the stated assumptions. hTC and hTD are naturality in the fixed tensor input, and
no comparison in the first tensor variable is imposed. Both shift equalities have
source K⊗P[n] or L(K⊗P[n]) and the required shifted target. For the two naturality
equalities, checked that tensor maps first change K/E and then P, and that the
square hypothesis is precisely `c ≫ b = L.map a ≫ c'`. All four equalities and all
quantified cases are present. No mathematical mismatch or statement change was
found in this second pass.
