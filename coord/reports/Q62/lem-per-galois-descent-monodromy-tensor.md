## Worker report

The module `Sheaf.ConstructibleSheaf.GaloisDescentMonodromyTensor` states
`AlgebraicGeometry.GaloisModuleDescent.galois_descent_monodromy_tensor`.
Its proof is `sorry`. Every auxiliary definition contains actual data. The node's
natural-language statement and dependency lists are unchanged; its only changed field
is `lean`.

The statement uses the existing descent equivalence and natural local trivialization
from `exists_galoisCoverModuleDescent`. The parameters `E`, `e`, and
`IsDeckNormalized c R E e` package exactly that dependency's supplied equivalence,
trivialization, and displayed deck formula. They impose no new condition on the cover,
ring, or representation. Universal quantification over this normalized presentation
avoids choosing an arbitrary descent equivalence from an existence proof. The canonical
small-site/ordinary-site transport is supplied as real helper definitions in the owning
module, as authorized by the brief's missing-helper rule.

Hypothesis and clause correspondence:

- The scheme is `{S : Scheme.{u}}`. `[ConnectedSpace S]` includes nonemptiness;
  `[IsNoetherian S]` is the existing locally Noetherian plus quasi-compact scheme
  predicate. No Noetherian hypothesis is imposed on the coefficient ring.
- The connected finite etale Galois cover is `c : S.FiniteEtale` with
  `[PreGaloisCategory.IsGalois c]`. Its total scheme is `c.obj.left`, its structural
  map is `c.obj.hom`, and its deck group is `Aut c`. The recorded IsGalois predicate
  includes categorical connectedness, which the recorded scheme/connected-object
  comparison identifies with connectedness of the total scheme. Its evaluation action
  on the geometric fibre is simply transitive, as specified by `def-galois-object`.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `t : Spec (.of Ω) ⟶ c.obj.left`. Its image point is literally `t ≫ c.obj.hom`.
- The fundamental group is `Aut (FiniteEtale.fiber (t ≫ c.obj.hom))`, with the existing
  profinite evaluation topology. This is the finite-etale version reexported by the
  recorded FLC fibre interface and identified with its FLC version by the recorded
  fibre equivalence, as also used by the monodromy dependency itself.
- The ring is `R : CommRingCat.{u + 1}`, with `n : ℕ`, `0 < n`, and `(n : R) = 0`.
  Using positive naturals for a positive integer loses no case. Representations
  `Rep.{u + 1} R (Aut c)` include every R-module with an R-linear deck-group action
  in the common site/coefficient universe; no finite generation is required.
- The descended R_S-module sheaf is `(realization c R E).obj V`. `Modules`, `Site`,
  `topology`, `Trivialized`, `realization`, `coverObject`, `deckMap`, and
  `constantSection` are the recorded dependency's declarations, not new versions.
  `trivialization` names precisely its natural isomorphism on the slice over the cover,
  in the direction constants to the restricted descended sheaf. Etale inverse image is
  this restriction, as stipulated by the recorded inverse-image/restriction comparison.
- `coefficientPresheaf` applies Mathlib `PresheafOfModules.restrictScalars` along
  `constantCoefficientUnit`. `coefficientSheaf` retains the abelian sheaf and maps.
  `etaleRealization` is then Mathlib's `Equivalence.sheafCongr` transport along the
  existing `equivSmallModel` equivalence. This connects the already recorded
  small-site ringed-module encoding to the monodromy dependency's ordinary-site
  ModuleCat-valued encoding, without changing either site or imposing universe equality.
- `stalk` composes that realization with the existing `pointSmallEtale.sheafFiber`.
  `constantGerm` explicitly uses the recorded `pointedEtaleGerm` at `(c.obj,t)`;
  its target is definitionally the same pointed-neighbourhood colimit. Thus it is
  exactly the germ of `liftedConstant`, namely the inverse trivialization applied to v.
- Clause 1 starts with `∃ θ : Aut (FiniteEtale.fiber ...) →* Aut c` and
  `@Continuous _ _ inferInstance ⊥ θ ∧ Function.Surjective θ`. The explicit bottom
  topology on the finite deck group is its discrete topology. The next conjunct pins
  theta by `(fiber s).map (θ g)⁻¹.hom t = g.hom.app c t`, implementing the inverse deck
  convention in the node's proof. These clauses precede every coefficient parameter;
  theta consequently depends only on the marked cover, not on R, V, E or e.
- The existential `cstar` is characterized on every finite-etale object and every
  geometric-fibre element by the actual `FiniteEtale.pullbackFiberIso`. This uniquely
  specifies the canonical induced fundamental-group homomorphism. `θ.ker = cstar.range`
  is precisely the requested kernel `c_* pi_1(T,t)`, not an arbitrary subgroup.
- `hL` states `IsIndFiniteEtaleModule` for each descended sheaf, using the monodromy
  dependency's existing definition of local system. `γ` is a family of R-linear
  equivalences to actual geometric stalks, with `γ V v = constantGerm ... V v`.
  Its following equation is naturality for every equivariant linear map `f`.
- `stalkAction` conjugates the action in the recorded
  `TorsionLocalSystemStalkEquivalence` by its actual `stalkIso`. The monodromy equation
  is `stalkAction ... g (γ V v) = γ V (V.ρ (θ g) v)`. It holds for any instance of that
  existing normalized interface; its `finiteGerm` field specifies the canonical action.
  Such an interface is supplied by `torsion_local_system_monodromy` under precisely
  the ring and scheme assumptions already present.
- Clause 2 gives `∃ i : ∀ V W, tensorSheaf R (T.obj V) (T.obj W) ≅ T.obj (V ⊗ W)`.
  `tensorSheaf` is exactly the recorded `siteSheafTensorRight` and `tensorSheafMap`
  composes its existing maps in the two variables. `V ⊗ W` is Mathlib's representation
  tensor, whose underlying module is `TensorProduct R V W` and whose action is
  `V.ρ.tprod W.ρ`, hence the required diagonal action.
- The equation involving all `f : V ⟶ V'` and `h : W ⟶ W'` is naturality in both
  variables. The last equation evaluates `i.hom` on `siteSheafTensorTmul` of the two
  `liftedConstant` sections and gives the lifted constant section `v ⊗ₜ[R] w`.
  It is the displayed pullback normalization: on the localized site it is the equation
  at its terminal object, and restriction gives the equation on every object over T.
  Constants locally generate the constant sheaves, so this specifies the full comparison.
- No `Finite`, `Fintype`, `Module.Finite`, or flatness assumption on R, V, or W occurs.

Recorded statement-dependency declarations used/read:

| Node | Module and declarations |
| --- | --- |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms |
| def-weil-connected-scheme | `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` |
| def-weil-pbc-noetherian-ring | `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; affine-ring ingredient of `AlgebraicGeometry.IsNoetherian` |
| def-galois-object | `Mathlib.CategoryTheory.Galois.GaloisObjects`: `PreGaloisCategory.IsGalois`; scheme interpretation in the recorded upstream `FundamentalGroup.Basic`/`Connected` |
| def-weil-geometric-point | `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; inline Spec-point encoding and `Scheme.SpecToEquivOfField` |
| def-galois-fibre-functor | `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`: `Scheme.flcFiber`, reexporting `Scheme.FiniteEtale.fiber`; comparison in `FiberEquivalence` |
| def-weil-sheaf-of-modules-category | `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` = `SheafOfModules` |
| def-weil-pbc-etale-site | `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale` |
| lem-per-galois-cover-module-descent | `Sheaf.ConstructibleSheaf.GaloisCoverModuleDescent`: `GaloisModuleDescent.exists_galoisCoverModuleDescent` and its existing auxiliary constructions listed above |
| def-weil-pbc-constant-sheaf | `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`; existing `SheafOfModules.constantCoefficientModule` and `constantCoefficientRing` |
| def-weil-pbc-inverse-image | `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`; its slice restriction interpretation from `Etale.upperStarIsoLocalizationRestriction` |
| def-weil-pbc-geometric-stalks | `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalk`, `pointedEtaleGerm`; the existing functorial `pointSmallEtale.sheafFiber` |
| lem-per-torsion-local-system-monodromy | `Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy`: `Scheme.TorsionLocalSystemStalkEquivalence`, `torsion_local_system_monodromy`, its `finiteGerm` field, and `IsIndFiniteEtaleModule` reexported from `IndFiniteEtaleLocalSystem` |
| def-pur-sheaf-tensor-product | `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, reexporting `siteSheafTensorRight`, `siteSheafTensorSecondMap`, `siteSheafTensorTmul` |
| def-weil-pbc-module-tensor-product | `Mathlib.LinearAlgebra.TensorProduct.Defs`/`Basic`/`Map`: `TensorProduct`, its pure tensors, `lift`, `ext'`, maps; `Rep.Basic` supplies the existing diagonal representation tensor |

The public dependency imports reexport the statement interfaces. The direct non-public
proof imports include Galois transitivity, the fundamental-group/fibre equivalence,
module sheafification tensor, localized tensor restriction, constant geometric stalks,
finite-etale finite limits and set-sheaf descent. Other recorded proof dependencies
already come through the two main dependency modules; the node
`lem-weil-pbc-site-constant-restriction` currently has no separate recorded module to import.
The full seven-step node proof, including its inverse deck convention and overlap graph
argument, is preserved in the theorem docstring.

Searches performed:

- `msearch.py ... leanfinder "Monodromy of modules descended along finite Galois covers
  and natural tensor isomorphisms"`: eight results, including abstract Galois action
  and evaluation lemmas; none states module-sheaf descent monodromy or its tensor clause.
- `msearch.py ... loogle "CategoryTheory.PreGaloisCategory.functorToAction"`: twelve
  results giving finite-set actions and their properties, not this statement.
- `msearch.py ... grep "monodromy|[Gg]alois.*[Dd]escent" AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch "Monodromy of module sheaves descended along a finite
  Galois cover preserves tensor products"`: eight tensor/sheaf results, none this lemma.
- `rg` on `WeilConjectures/` and `lean/Sheaf/` for `GaloisModuleDescent`, `monodromy`,
  the exact node id, `GaloisDescentMonodromy`, and `galois_descent_monodromy`: found the
  recorded descent and local-system dependencies and specialized finite-field torsor
  descent, but no existing declaration of the item. The specialized
  `exists_module_descent_stalk_functor` has prime-field finite-dimensional hypotheses
  and lacks this quotient/tensor statement, so it cannot serve as an existing match.
- Read Mathlib's `ConstantRingModuleRestriction` candidate in the project: it applies
  to `constantSheaf J RingCat`, whereas the descent module uses the ring underlying
  `constantSheaf J CommRingCat`. The helper applies the existing scalar restriction
  directly to that dependency's specified unit; it does not introduce another module
  category, constant sheaf, stalk, or tensor.

Source checks: read Stacks `pione.tex`, Section 03SF and the discussion around Lemma
0BN2; `sites-modules.tex` Tags 0GMW and 03EL; and the local ILO PDF text at XVII
7.2.1--7.2.4, pp. 301--302. These give finite-Galois quotients, the ind-finite geometric
monodromy equivalence, finite-cover locality, and the ordinary tensor comparisons.
The source agrees with the node, so no statement correction or disputed flag is needed.

Edge cases: the empty base and empty Galois total space are excluded by connectedness;
no additional geometric point-existence assumption was inserted. The identity cover
and trivial deck group are included. Zero modules and the zero ring (including n = 1)
are included; n = 0 is excluded exactly as in the node. Infinite coefficient rings,
infinite modules, nonflat modules and noncommutative deck groups are retained.
The inversion in theta was checked against commuting left deck and monodromy actions:
a_(gh) = a_h a_g and contravariant restriction acts by rho(a inverse). Pure tensors
generate the ordinary tensor without any flatness assumption. The site-size transport
uses precisely the dependency's `SmallModel.{u+1,u,u+1}` and coefficient size u+1;
it does not identify the original site's object and morphism universes.

Validation: the complete module compiled cleanly, both as the wrapper's sandbox module
and as `Sheaf.ConstructibleSheaf.GaloisDescentMonodromyTensor`, with `scompile.py`
(approximately seven seconds each). Only the main theorem has a postponed proof.

## Second reading by Q62

I reopened the node and completed module for a separate clause-by-clause pass in this
worker session; the independent mathematical review is the maintainer's delivery review.
I checked the explicit Noetherian/connected hypotheses, finite-etale/Galois predicate,
algebraically closed geometric lift, positive annihilator, and arbitrary coefficient
modules against the node. I checked the quotient's quantifier before R, its inverse
fibre-action characterization, and the canonical cstar kernel equation. I then checked
that gamma is an R-linear equivalence fixed by actual germs and natural on all Rep maps,
and that the action formula uses the existing normalized monodromy, not an unrelated
representation. Finally I unfolded the tensor helpers to the existing sheaf tensor,
verified the diagonal action in `Rep.Basic`, and checked both the two-variable naturality
and the terminal-slice pure-tensor equation, which restricts over the entire cover.

During drafting I replaced the directly written `toPresheafFiber` germ with the node's
recorded `pointedEtaleGerm`; compilation confirms that its target is definitionally the
same geometric stalk. I also supplied an explicit existing dense-subsite instance for
the site equivalence, resolving elaboration without an added hypothesis or an axiom.
No mathematical mismatch or node correction was found. No dependency node or independent
notion needs a new statement: the helper declarations only connect the recorded
encodings and name the maps and equations already specified by this item.
