## Worker report

The module `Sheaf.AlgebraicGeometry.EffectiveActionNormPencil` states
`AlgebraicGeometry.Scheme.Modules.effective_action_norm_pencil`, with `sorry` as its
entire proof. It uses the existing ordered orbit bundle, norm, projective-coordinate
morphism and factorwise base-change construction. It neither changes the node's
mathematical statement nor repairs any existing dependency record.

Hypotheses and objects, matched individually:

| Node | Lean |
| --- | --- |
| Integral scheme S, with its function field K | `S : Scheme.{u}`, `[IsIntegral S]`, `S.functionField`; the generic point map is `S.fromSpecFunctionField : Spec S.functionField ⟶ S`. |
| Integral Y | `Y : Scheme.{u}`, `[IsIntegral Y]`. |
| Dominant separated p:Y→S | `p : Y ⟶ S`, `[IsDominant p]`, `[IsSeparated p]`; Mathlib dominance is dense image, and separatedness is a closed diagonal. No finite-type or flatness hypothesis is imposed. |
| Finite J acting over S | `J : Type v`, `[Group J]`, `[Finite J]`, `ρ : J →* Aut (Over.mk p)`. The Over category supplies exactly the equations over S. |
| G is the image, not J and not an arbitrary faithful quotient | `ρ.range`, with its inherited group law and subtype homomorphism; `pencilEffectiveAction ρ` forgets the over-S structure to an actual automorphism of Y. Its finite instance is transported along the existing surjective `ρ.rangeRestrict`. |
| Generic fibre C=Y×_S Spec K | `(Over.pullback S.fromSpecFunctionField).obj (Over.mk p)`; its underlying scheme is `Limits.pullback p S.fromSpecFunctionField`. |
| Arbitrary invertible L | `L : Y.Modules`, `[L.IsInvertible]`, using the recorded Scheme.Modules notion. No ampleness or linearization on L is assumed. |
| Every tensor degree n, including zero | All three section statements quantify over `n : ℕ`. |
| Any pair a,b whose norms generate | `a b : (L.tensorPow n).sections`, with exactly `Epi (M.freeHomEquiv.symm (pencilSectionPair M N(a) N(b)))`. This is generation as sheaves, not surjectivity on global sections. |
| Arbitrary base change, including opens | `∀ (T : Scheme.{u}) (t : T ⟶ S)` with no conditions on T or t. Open restriction is the instance `T=U.toScheme`, `t=U.ι`. |
| Every m≥1 | `∀ (n m : ℕ) (_hm : 1 ≤ m) (a : (L.tensorPow n).sections)`. |

Conclusion clauses, in the order in the theorem:

1. The leading `Function.Injective` is the restriction homomorphism from the actual
   image subgroup `ρ.range` into automorphisms in the Over category over `Spec K`.
   It is the composite of `ρ.range.subtype` with the actual functorial `mapAut`
   of `Over.pullback S.fromSpecFunctionField`; no replacement map is supplied.
2. `pencilOrbitBundle (pencilEffectiveAction ρ) L` is exactly B, in the enumeration
   and parentheses fixed by `def-sfb-pencil-orbit-bundle-norm`.
   `pencilNormSection (pencilEffectiveAction ρ) L n a` is exactly N_G(a), including
   its pullback-power and distribution comparisons. Existential `_hB`, `hBn`
   assert invertibility of B and its powers; they are proofs, not input data.
3. `pencilLinearization` is constructed by the normalized pullback-composition
   comparison and right multiplication of labels, followed by the unique factor
   permutation characterized on local pure tensors. The identity equation compares
   its hom with `pencilActionIdentityIso`. The next universal equation is
   λ_(hk) = composition-comparison ≫ k*(λ_h) ≫ λ_k, the node's contravariant
   cocycle, with `(gh)(y)=g(h(y))`.
4. The following equality transports the actual pullback of N_G(a) through
   `pencilPowerLinearization` and obtains N_G(a). This iso is precisely the
   canonical pullback-power comparison followed by the nth tensor power of λ_h.
5. For every generating norm pair and `j : J`, the section-coordinate morphism
   `pencilCoordinateMorphism p ...` satisfies `(ρ j).hom.left ≫ φ = φ`.
   Its target is the recorded `ProjectiveLine S = ℙ(ULift (Fin 2); S)`;
   this is equality of scheme morphisms, with the S component included.
6. For every `t:T→S`, `pencilOrbitBaseChangeIso` identifies v*B with the orbit
   bundle formed on Y_T. The same `ρ.range` indexes both sides. In particular it
   is NOT replaced by the image of the action on Y_T.
   The first base-change equation says the factorwise comparison intertwines
   λ_h with λ_(h,T), using the exact action square and normalized composition
   comparison `pencilCommutingPullbackIso`.
7. The next base-change equation transports the pullback of N_G(a), using the
   nth power of the exact bundle comparison, to `pencilBaseChangeNorm ρ t L n a`.
   This latter section is constructed by first pulling a back with the canonical
   power comparison and then taking the norm of the induced action. Thus the
   equation compares the required actual sections, not arbitrary identified ones.
8. The final base-change clause gives `hNT`, generation of the two base-changed
   norms. Its equation is `φ_T ≫ ProjectiveSpace.map _ t = v ≫ φ`.
   By its definition `pencilCoordinateMorphism (pullback.snd p t)` already has
   structure component `pullback.snd p t`. Those two components and the
   projective-space pullback property say exactly that φ_T is the base change of φ.
9. The last equation is N_G(a^m)=N_G(a)^m in B^(nm).
   `pencilSectionPower` uses the existing `tensorPowSection` on section morphisms
   and the inverse of `tensorPowMulIso`, so both sides use the prescribed
   concatenation, with no unconstrained power map or comparison.

Canonical constructions and deferred proofs:

- `pencilLocalTensor` is a real list recursion, using `tmulSection` and the unit
  section 1. It does not duplicate the orbit bundle construction.
- `existsUnique_pencilPermutationIso` postpones the universal-property proof of
  the canonical permutation in node steps 3–4. Its condition quantifies over EVERY
  open U and EVERY family of local sections of the translated factors. These local
  pure tensors locally generate the tensor sheaf, so the condition determines
  its hom and hence the whole isomorphism uniquely. Global sections alone would
  not be a sufficient characterization. The selected iso is therefore not a
  choice from mere existence, and this adds no independent mathematical input.
- The other helpers are explicit specializations/composites of the recorded
  pullback, power, action-image and base-change constructions. Every declaration
  is listed in `lean.declarations`, has a source/blueprint docstring and is public.
- Only `existsUnique_pencilPermutationIso` and `effective_action_norm_pencil` have
  `sorry`; each is a complete named statement with its natural-language proof.
  The main docstring follows all nine recorded proof steps and names their nodes.

Dependency declarations used:

| Node | Module and declarations |
| --- | --- |
| def-sfb-pencil-orbit-bundle-norm | `Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil`: `Scheme.Modules.pencilGroupElements`, `pencilTranslateTensor`, `pencilOrbitBundle`, `pencilTranslatePowerIso`, `pencilTranslateSection`, `pencilNormSection`. The same module's `pencilSectionPair` and `pencilCoordinateMorphism` specialize the already recorded generating-section and projective-space constructions. |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`. |
| def-sc-function-field | `WeilConjectures.AlgebraicGeometry.FunctionField`, reusing `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField` for the arbitrary integral-scheme clause. `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.fromSpecFunctionField`, the actual `fromSpecStalk` at the generic point. The component-product definition is not the carrier for integral S. |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper` and `Separated`: `AlgebraicGeometry.IsSeparated`; no properness condition is inserted. |
| def-pc-base-change | `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: `baseChange_morphism_projections`, together with Mathlib's `Over.pullback`, `Functor.mapAut`, `Limits.pullback`, `pullback.fst`, `pullback.snd`. |
| def-sc-invertible-module | `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`, `tensorPow`, `tensorPowMulIso`. |
| def-weil-pbc-generating-sections | `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`: `SheafOfModules.GeneratingSections`, encoded by its `epi` condition on `freeHomEquiv.symm`. |
| def-weil-pbc-morphism-to-projective-space-by-sections | `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`: `ProjectiveSpace.homOfGeneratingSections`, via the real `pencilCoordinateMorphism` specialization. |
| def-pc-module-pullback | `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`, `tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`, `tensorPullbackSectionId`. |
| def-sc-tensor-pullback-power-comparison | `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`: `boundaryPullbackComparison`, `boundaryPullbackTensorIso`, `boundaryPullbackPowIso`; its `boundaryTensorPowIso` gives actual tensor powers of an iso. |
| def-sfb-orbit-tensor-base-change-comparison (new ownership record) | `Sheaf.AlgebraicGeometry.SeparatingPairOpen`: `AlgebraicGeometry.normPencilTranslateBaseChangeIso`, used without copying its definition. |

All recorded proof-dependency modules are imported. In particular the separated
extensionality statement is from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated`;
the fraction-field lemma is Mathlib's `functionField_isFractionRing_of_isAffineOpen`;
tensor invertibility is `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`;
the symmetric tensor structure is `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`;
the generating-fibre criterion is
`WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre`; and the projective
functor of points is `Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints`.
No proof import is omitted for a cycle. The new base-change definition node prevents
using the separating-pair theorem itself as a statement dependency merely for its helper.

Edge cases checked before and after writing:

- J trivial or an entirely ineffective J: the index is its trivial IMAGE group,
  so the unit-tail orbit tensor has one translated factor; no accidental |J| factors.
- A noncommutative group: Aut multiplication is reverse categorical composition,
  and right translation g↦gh therefore gives exactly λ_(hk)=k*λ_h followed by λ_k.
- n=0: tensor power is the structure module, but a is an arbitrary global function.
  The norm remains the product of its translates. For a=0 or a=2 with trivial G
  it is 0 or 2, not forced to be 1. The power identity remains the ordinary product
  identity. No positive-degree restriction was inserted.
- m=1: the same prescribed tensorPowMulIso identifies the two section expressions.
- a=b or a=0: permitted whenever the exact stated pair-generation hypothesis holds.
- Arbitrary empty, nonreduced or nonflat T: the base-change quantifier has no
  integrality or nonemptiness requirement. Distinct elements of G may induce the
  same automorphism on Y_T and remain distinct tensor labels.
- Empty list and empty finite index type in the permutation helper: unit comparisons
  and section 1 determine the identity on the unit sheaf. Finite groups themselves
  have their required identity element.
- S a field and p the identity; separatedness remains precisely relative separatedness.
- All schemes and modules use u, while the ORIGINAL finite group has independent
  universe v. Its image has the actual universe of Aut_S(Y); no artificial equality
  of those universes and no bounded cardinality assumption is imposed.

Searches for the item (msearch.py, Q51/item):

- LeanFinder: “Finite group orbit tensor products of invertible sheaves have canonical
  linearizations and invariant norm sections compatible with base change and powers”.
  Eight hits, including representation-theoretic coinvariant tensor identities and
  Rep norm maps. None is a statement about orbit bundles or generic scheme actions.
- Loogle: `AlgebraicGeometry.Scheme.Modules.pencilNormSection, CategoryTheory.Functor.mapAut`.
  Zero hits; the service does not index the project's pencilNormSection declaration.
  The local source was read in full instead.
- Grep: `orbit.*[Bb]undle|norm.*[Ss]ection|linearization|linearisation` in Mathlib
  AlgebraicGeometry. One irrelevant EllipticCurve/NormalForms documentation match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for pencilNormSection,
  pencilOrbitBundle, linearization and base-change comparisons found the existing
  constructions in AmpleCurveTwoSectionPencil and SeparatingPairOpen. Neither
  states this combined result. `grep -rn` for the item id in WeilConjectures found
  no match. New helper declaration names were also searched in Mathlib,
  WeilConjectures, Sheaf and `dag/lean_names_upstream.json`: no collisions.
- The new definition node records the additional LeanSearch, LeanFinder and grep
  queries and their actual outputs, together with DAG and blueprint searches.

No STATEMENT-DISPUTED finding. No mathematical statement correction. The first compile
exposed expensive unfolding of tensorPullback and absence of a Finite range instance;
marking that existing functor locally irreducible for elaboration and transporting
Finite along the surjective range restriction repaired both. The 60-second timeout
and default heartbeat bound were not increased. The complete module compiled cleanly
in both sandbox and library modes (3.5 and 3.7 seconds before final documentation/imports).

## New nodes

`def-sfb-orbit-tensor-base-change-comparison` registers the ALREADY EXISTING definition
`AlgebraicGeometry.normPencilTranslateBaseChangeIso` in
`Sheaf.AlgebraicGeometry.SeparatingPairOpen`, with `existing: true` and its exact signature.
It defines the ordered factorwise comparison for an equivariant morphism and an arbitrary
list of translated module factors: pullback of the unit on the empty list, and the tensor
comparison plus the commuting action square and recursive tail on a cons. At the fixed
finite enumeration it identifies the orbit bundles. Its source is Stacks modules.tex,
Tags 01CA and 01CD, read locally. There is no new Lean module and no copied definition.
The existing theorem-node listing of this helper did not provide a definition-node
owner. LeanSearch/LeanFinder returned tensor and fibre-product facts, Mathlib grep had
no match, project grep found exactly this real definition, DAG grep found only the
separating-pair theorem's record, and blueprint_refs.py search 'orbit tensor' returned
zero blueprint nodes. It is added to the item's statement dependencies, along with the
already recorded module-pullback and tensor-pullback-power definition nodes explicitly
used in the canonical maps.

## Second reading by Q51

This is the author's second pass, not an independent agent's review. The dispatcher brief
requires a single worker, forbids starting other agents, and assigns independent review
to the maintainer. The table and numbered clause match above were checked with both the
node and complete file open. In this pass the degree-zero sections, right-translation
cocycle orientation, image group after nonfaithful base change, sheaf-level Epi generation,
and both components of the relative pencil were checked explicitly. The new definition
node was checked against the entire existing recursive definition and its docstring;
its signature is copied verbatim. No hypothesis or conclusion was changed. Independent
maintainer review remains the next review step under the supplied brief.

Dry-run repair: the current server schema requires `import_flags` on new definition
nodes (tools/stage2_delivery.py, schema update 2026-10-23). Added the required empty
list; no flags apply and no mathematical field changed.
