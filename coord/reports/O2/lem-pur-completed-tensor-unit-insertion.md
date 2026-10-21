## Worker report

The module `Sheaf.Paper.CompletedTensorUnitInsertion` states
`CategoryTheory.ConstantCompletion.completedTensorUnitInsertion`. Its only theorem
has proof `sorry`. All other declarations are fully written definitions or transparent
specializations of published constructions. No node statement or dependency list changes.
The named helper predicates expand the equations of this node's proof, rather than
postulating any completion, inverse image, tensor, or comparison as a hypothesis.

Hypothesis and clause correspondence:

| Node | Lean |
|---|---|
| Two sites small in the module universe | `{C E : Type u} [SmallCategory C] [SmallCategory E]`, topologies `JC`, `JD`; the source site is C and target site E. This is the size convention already used by the recorded completed-pullback interface. |
| A commutative Noetherian ring and an arbitrary ideal | `(A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)`. |
| Positive quotients A_n | Published `finite JC A I n` is the constant sheaf of `A / I^(n+1)`. Its index zero is the first positive quotient. There is no extra quotient or perfectness hypothesis. |
| Morphism of topoi | Set-sheaf inverse/direct images `L`, `V`, `(adj : L ⊣ V) [PreservesFiniteLimits L]`. The existential `F : InverseImageData L` supplies its coherent algebraic lifts and canonical constant-ring identification. It is a conclusion, not an assumption. |
| Ordinary unbounded module derived categories | Published `D (constant JC A)` and `D (constant JD A)`, where `Mod` is `ringedSiteModules` and `D` is exactly `DerivedCategory` with `HasDerivedCategory.standard`. |
| Canonical derived inverse image | `(derivedPull F V adj (constantMap F A)).functor`, the existing universal left derived functor with its cochain computation transformation. No arbitrary derived functor is substituted. The ordinary derived right adjoint and counit are the ones provided by `completedPullbackAdjunction`; this node's displayed equations only use the left functor. |
| Ordinary derived tensor and constraints | `constantDerivedMonoidal` and `constantDerivedSymmetric` transparently specialize `RingedDerivedNative.monoidal` and `.symmetric` to the standard localization. `constantDerivedTensor` is their ordinary tensor bifunctor. No alternative tensor is constructed. |
| Specified ordinary pullback tensor comparison mu | Existential `k : ConstantTensorData F A` is the existing pure-generator-normalized `CanonicalRingedTensorComparison` for `pull F (constantMap F A)`. `ConstantTensorNormalization F V adj A k μ` identifies the existential natural isomorphism `μ` on every pair of flat-term K-flat representatives, using the published native representative tensor isomorphisms and `derivedPull.comparison`. The equation, in Lean composition order, is `L(rY) ≫ μ ≫ tensor(eP,eQ) ≫ rX.inv ≫ Q(k.total) = eTot`. Since `k.total` is oriented opposite to c in the node's proof, this is precisely its Tag 07A4 normalization. It cannot be replaced by minus mu. |
| Completion reflector and its particular unit | `completion JC A I false`, `completionUnit JC A I false`, and their JD versions, exactly from `ConstantCompletionEquivalence` and `CompletedPullbackAdjunction`. `false` means completion over the ordinary constant A coefficients. |
| Full complete subcategory | The existing predicate `IsComplete (quotient JC A I 0)` and `ObjectProperty.FullSubcategory`; likewise on JD. Its definition is local derived internal-Hom completeness for the actual kernel ideal I. |
| Left and right tensor-unit insertions for arbitrary inputs | In `CompletedTensorAssertions`, `hLeft`, `hRight`, `hLeft'`, `hRight'` assert `IsIso` of `tensorInsertLeft` and `tensorInsertRight` for every object pair on each site. The helpers are exactly `T.map (η.app V ⊗ₘ 𝟙 W)` and `T.map (𝟙 V ⊗ₘ η.app W)`. Their naturality is the naturality of η, bifunctorial tensor, and functorial T; objectwise invertibility therefore gives natural isomorphisms, without an extra naturality assumption. |
| Pullback insertion | The next conjunct is `∀ V, IsIso (T'.map (L.map (η.app V)))`, with L here the derived inverse image. This is exactly `C_X u*(η_Y,V)`, on arbitrary ordinary derived inputs. It is again a natural transformation by whiskering the specified unit. |
| Completed tensor and its unit | `CompletedConstraintModel` fixes the completed tensor object to `T.obj (V.obj ⊗ W.obj)`, its morphisms to `T.map (f.hom ⊗ₘ g.hom)`, and the unit object to `T.obj (𝟙_ B)`. |
| Actual completed constraints | The same predicate fixes the associator to `inv(left insertion) ≫ T.map ordinaryAssociator ≫ right insertion`, symmetry to `T.map ordinarySymmetry`, and both unitors to inverse unit insertion followed by `T.map ordinaryUnitor` and inverse η of the complete input. These are precisely proof step 5. `HEq` is only used to compare underlying arrows whose endpoints are identified by the preceding tensor-object equations; it is not an unspecified comparison. |
| Natural completed comparison and its displayed source/target | `μc : tensor B ⋙ T ⋙ L ⋙ T' ≅ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T'`, thus component `C_X u* C_Y(V tensor W) ≅ C_X(C_X u*V tensor C_X u*W)`. This holds on all ordinary inputs, hence in particular on the complete inputs of the node. |
| Normalization and uniqueness | The equation is `T'.map (L.map (η.app (V ⊗ W))) ≫ μc.hom.app (V,W) = T'.map (μ.hom.app (V,W) ≫ (η'.app (L.obj V) ⊗ₘ η'.app (L.obj W)))`. A separate conjunct quantifies every natural isomorphism ν of this same type and concludes `ν = μc` from this equation. |
| Unit comparison induced by the ordinary unit | The existential ordinary unit iso e is fixed by both ordinary left/right action-unit equations. The completed iso ec satisfies `T'.map (L.map (η.app 1)) ≫ ec.hom = T'.map e.hom`, exactly `e_c=C_X(e) a_1^(-1)`. Invertibility of a_1 already fixes ec uniquely. |
| Associativity and tensor-unit coherence | `CompletedPullbackCoherence` asserts an `OplaxMonoidal` structure on `completeInverse`, whose cotensorator has underlying arrow exactly `μc` and whose unit is exactly ec. Mathlib's fields `oplax_associativity`, `oplax_left_unitality`, `oplax_right_unitality` are the required equations, for every complete input. All these arrows are the separately supplied isomorphisms. |
| Symmetry coherence | The last equation of `CompletedPullbackCoherence` is `δ(V,W) ≫ β(FV,FW) = F(β(V,W)) ≫ δ(W,V)`. The completed symmetries are fixed to completion of the ordinary signed swaps. |
| Coherence of the completed categories themselves | Their `MonoidalCategory` structures include naturality, pentagon and triangle, and their `SymmetricCategory` structures include involution and both hexagons, for the explicitly normalized constraints. |
| No perfectness | There is no perfectness, flat-quotient, boundedness, finite Tor dimension, nonzero-ring, or nontrivial-ideal hypothesis anywhere in the theorem. |

Dependency declarations read and used:

- `def-weil-size-convention` is a metatheoretic convention, explicitly recorded with no
  declaration; the universes and small sites implement it.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the recorded Noetherian notion.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, through
  published `ConstantCompletion.constant`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, through
  the published `ConstantCompletion.Mod`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, through `ConstantCompletion.D` and `.Q`.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact` and the
  canonical tensor comparison machinery in `RingedTensorEdge.tensorComparison`; the
  module is imported as the recorded statement dependency. The present theorem's
  representative normalization uses the same `CanonicalRingedTensorComparison.total`
  and derived computation maps, directly at the standard localization.
- `Sheaf.Paper.CompletedPullbackAdjunction`:
  `CategoryTheory.ConstantCompletion.completedPullbackAdjunction`, using its imported
  `InverseImageData`, `constantMap`, `derivedPull`, `completion`, `completionUnit`,
  `IsComplete`, and full complete subcategories verbatim. No record repair is needed.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `ringedDerived_closed_symmetric_monoidal`; the additional public import of its native
  implementation exposes `RingedDerivedNative.monoidal`, `.symmetric`, `.tensorIso`.
- Proof imports: `RingedInternalHomDerivedComplete`;
  `SecSmoothPurity.CochainPullbackTensorCoherence`;
  `SiteDerivedTensorDescentIndependentCoefficients`. The proof-only dependency
  `lem-weil-pbc-pullback-tensor-canonical-shift-unit` has no Lean record or Mathlib match
  in the supplied DAG, so there is no recorded module to import for it. Its ordinary
  representative normalization is spelled out in this node's own helper predicate;
  its shift theorem is not restated or needed to type the item.

Edge cases checked before and after writing: I=0 (completion is the identity up to its
unit), I=A (complete category is zero), nilpotent I (eventually constant quotient tower),
A the zero ring, the identity topos morphism, arbitrary unbounded/zero inputs, and
quotients not perfect over A. For example A=k[e]/(e^2), I=(e), has a nonperfect first
quotient but nilpotent completion; none is excluded. There is no zero-power quotient:
the existing tower indexes I^(n+1). Tensor insertion and pullback insertion are asserted
on arbitrary derived objects, not merely on complete ones.

Searches (all on 2026-10-21; exact wrapper queries are also in searches.jsonl):

- LeanFinder: `Derived completion unit induces natural tensor insertion isomorphisms
  and coherent completed pullback tensor comparison`: eight ordinary adic-completion
  results including `AdicCompletion.ofTensorProduct_naturality`, `ofTensorProduct`,
  `ofTensorProductEquivOfFiniteNoetherian`; no derived-completion/topos theorem.
- Loogle: `CategoryTheory.MonoidalCategory, CategoryTheory.Functor.OplaxMonoidal`:
  twelve hits, including the existing `Functor.OplaxMonoidal` coherence structure used
  here; no completion theorem.
- Mathlib grep via msearch, query `completion.*tensor|tensor.*completion|Day.*[Rr]eflection`,
  subdirectory `CategoryTheory`: five hits in `Monoidal/Braided/Reflection.lean`.
  Day reflection is an abstract tool and does not specify these quotient completions,
  pullback insertions, or the normalized canonical comparison.
- LeanSearch: `Derived completion is a symmetric monoidal localization and completed
  pullback preserves tensor products coherently`: eight generic monoidal localization
  results; none establishes the node's hypotheses or its normalization.
- Project `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for completed tensor/unit
  insertions and completion/monoidal coherence found coefficient-specific completed
  comparisons and ordinary cochain interfaces, but no theorem on these arbitrary
  constant Noetherian coefficients and small sites. Exact new names were searched
  in both roots and `dag/lean_names_upstream.json`, with no matches.
- `grep -rn 'lem-pur-completed-tensor-unit-insertion' lean/WeilConjectures`: no hit.

Source read: Stacks algebraization.tex, `lemma-derived-complete-internal-hom` (099A)
and `remark-completed-tensor-product` (099G), plus the item's entire nine-step proof
and both recorded statement-dependency interfaces. The fixed associator/unit formulas
come from this item's proof step 5, which already supplies the constraints implicit
in its statement; no statement correction or new node is needed. No disputed statement.

Validation: prescribed scompile.py compiled both sandbox and final module cleanly
(12.9 and 13.9 seconds), without warnings. Every universe and binder is explicit;
autoImplicit is false. There are no local instances, private definitions, local
notations, additional axioms, inline sorry data, or non-sorry theorem proofs.

## Second reading by O2

I separately reread the node, every helper body, and the final theorem after successful
compilation. This is the delivering worker's second pass; the dispatcher's independent
maintainer review is still required, and no other agent was started.

The three often-missed clauses are present: both tensor insertions hold for arbitrary
ordinary inputs on BOTH sites; μc has a separate uniqueness clause among natural
isomorphisms; and BOTH unit laws are fields of the oplax monoidal structure whose
underlying comparison is fixed to μc. The completed unit is C1, with ec normalized
against the ordinary unit e. The completed associator is inverse left insertion,
ordinary associator, then right insertion, in Lean's left-to-right composition order.
I checked the same direction in the representative normalization: k.total has the
inverse orientation to the displayed c, explaining its position after rX.inv.
The full-subcategory objects and arrows have their existing inherited category;
HEq compares their underlying ordinary-derived arrows after the explicit object
identifications and introduces no new isomorphism choices. The ordinary structures
are transparent specializations, and the geometric F, ordinary k, μ, and all completed
structures are conclusions, not additional hypotheses. No mathematical mismatch found.
The only revisions during compilation were explicit native-module visibility,
projection-argument syntax, and explicit equal universe parameters for native tensor
representatives; these did not change hypotheses or conclusions.
