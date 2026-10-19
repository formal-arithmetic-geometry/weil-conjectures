## Worker report

Repair of the return for immutable head `894eb52182d2`, points H3 and H8.
The main theorem now uses canonical maps throughout. There are no `kZ`, `kW`,
`kZ_iso`, or `kW_iso` parameters. The natural-language item is unchanged.

The main module is `Sheaf.Paper.KunBcKunnethCompat`, declaration
`AlgebraicGeometry.Etale.kun_bc_kunneth_compat`. Clause-by-clause rendering:

- The separably closed base field is `{k : Type u} [Field k] [IsSepClosed k]`.
  The level and invertibility are `(n : ℕ) (hn : 0 < n) [Invertible (n : k)]`.
  `ULift.{u + 1} (ZMod n)` is the universe lift of exactly ℤ/nℤ, not an arbitrary ring.
- `aX`, `aU`, `aY` are the displayed structure maps to `Spec k`. Finite type of X and U
  is `[LocallyOfFiniteType] [QuasiCompact]` on their structure maps. Projectivity of Y
  is the recorded `[IsHProjective aY]`. The open immersion is `[IsOpenImmersion j]`.
  `hj : aU = j ≫ aX` makes j a morphism over the base.
- `hz : IsPullback q r aX aY` and `hw : IsPullback p s aU aY` specify Z and W,
  including both projections. `hq : p ≫ j = h ≫ q` and `hr : h ≫ r = s` specify
  h uniquely as the product map 1_Y × j. No chosen-product equality is assumed.
- F has type `Sheaf U.smallEtaleTopology (ModuleCat ... (ULift (ZMod n)))` and is
  placed in degree zero by `(DerivedCategory.singleFunctor _ 0).obj F`.
- E is the fixed coefficient object `constantComplex ... Y`, the constant unit.
- The two calls to `constantKunnethGlobalSectionsMap` with `(r,q,aY,aX,hz.w)` and
  `(s,p,aY,aU,hw.w)` render precisely k_Z and k_W. This definition composes the
  existing upstream `kunnethMap` with explicitly constructed canonical comparisons
  in module-valued cohomology and with the pullback-of-constant/left-unit constraints.
  It neither accepts an arbitrary map nor selects an isomorphism from `Nonempty`.
- `exactDerivedBaseChangeMap ... (CommSq.mk hq)` is the recorded unbounded exchange.
  Both inverse images in its type are the exact, termwise-descended inverse images.
- The Leray comparisons are `.hom.app` of
  `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso` for j and h. These are
  the canonical normalized comparisons, not parameters constrained only by IsIso.
- The equality is `k_Z ≫ RΓ_Z(Ex) ≫ λ_h = tensorHom (𝟙 _) λ_j ≫ k_W`.
  This is the node's displayed equality in Lean's composition order. Its stated
  equivalent identity follows by conjugating with the canonical isomorphisms.
- `HasSmallSiteSheafify` is the library's structural sheafification instance, and
  `HasInvertibleExponent` is the coefficient-size/library encoding of the stated
  invertible torsion exponent; neither is an assumption on F or on cohomological bounds.

H8: the module has the full `(blueprint: lem-kun-bc-kunneth-compat)` marker. The
statement docstring now reproduces all six DAG proof steps: module-valued point
identification; normalized Leray counits; proper Künneth and unit reduction;
monoidal/composition coherence on representatives; the double-adjoint calculation;
and the conjugated identity. Every declaration in the dependency module has its
own source and owning-node marker.

Dependency declarations used:

- `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`: `kunnethMap`,
  `constantSheafEquivalenceOfIsSepClosed`, `rightDerivedGlobalSectionsIsoOfIsSepClosed`.
  Its current full server source was read with `scompile.py --source`; the recorded
  general-base construction is reused unchanged, including its adjunction-mate formula.
- `WeilConjectures.SixFunctors.Etale.Derived.GlobalSections`:
  `rightDerivedGlobalSections`, `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`.
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence`:
  `DerivedCategory.tensorLeftCompMapDerivedCategoryIso`, through the upstream
  `mapDerivedCategoryObjTensorIsoDerivedTensor` interface, the canonical descent of
  the ordinary tensor comparison on K-flat representatives.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `constantComplex`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
  `leftDerivedUpperStarUnitIso`, `leftDerivedUpperStarIsoMapDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `exactDerivedBaseChangeMap`.
- The Mathlib declarations `IsSepClosed`, `IsOpenImmersion`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsPullback`, `DerivedCategory.singleFunctor`, `tensorHom`, and
  the monoidal unit constraints; upstream `IsHProjective` for the blueprint's
  finite-projective-space embedding convention.

Edge cases checked: identity squares now have the SAME canonical normalization on
both sides, so one can no longer independently multiply k_Z or k_W by 2 over ℤ/3.
The zero coefficient ring (n = 1), zero sheaf, empty schemes, identity open immersion,
nonconstructible F, and unbounded Rj_*F are all allowed. The source excludes n = 0;
`hn` does exactly that. No separatedness of X, nonemptiness, constructibility, or
boundedness assumption is introduced. Scheme and module universes retain the project
convention Scheme.{u}, coefficients/modules at u+1 and derived categories at u+2.

Searches during repair:

- `msearch.py ... leanfinder "canonical Kunneth external product on derived global
  sections of etale module sheaves"`: eight hits, all condensed-module monoidal
  infrastructure or Kähler base change, no matching statement or construction.
- `msearch.py ... loogle "CategoryTheory.Adjunction.rightAdjointLaxMonoidal"`:
  four generic monoidal-adjunction hits, no canonical étale global-sections Künneth map.
- `msearch.py ... grep "kunneth|Kunneth" AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "canonical Kunneth external product of etale cohomology
  commutes with base change"`: service unavailable (Internal Server Error).
- `rg` over Mathlib, the upstream `WeilConjectures/`, shared `lean/Sheaf/`, and the
  upstream declaration index for Künneth, external product, tensor/global-sections,
  `pointGlobalSectionsTensorIso`, `kunnethGlobalSectionsMap`, and
  `constantKunnethGlobalSectionsMap`. The general-base mate exists upstream;
  the displayed module-valued canonical maps do not. Existing module-valued Künneth
  results use `Nonempty` isomorphisms, which cannot fix the maps of this equality.
- Read full current server `Kunneth.Ordinary` and `Monoidal.Equivalence`, local
  `Derived.GlobalSections`, `Derived.Tensor`, `Derived.Coefficients`,
  `UpperStarMonoidal.Comparison`, and `ExactUnboundedExchange` signatures/docstrings.
  Opened Stacks Tags 0F1E, 0F14, 0DV0; the request for 0D6E returned HTTP 503.

## Dependency modules

`def-kun-kunneth-map`: `Sheaf.AlgebraicGeometry.KunnethGlobalSections` publicly imports
and reuses the upstream general-base `kunnethMap`. It supplies the missing canonical
module-valued interface: `pointGlobalSectionsTensorIso` conjugates the derived constant-sheaf tensor
comparison by the unit/counit of its canonical equivalence and the exact-derived
global-sections comparison;
`kunnethGlobalSectionsMap` transports the upstream mate by Leray and that tensor
comparison; `constantKunnethGlobalSectionsMap` applies the canonical pullback of
unit, left unitor and exact-inverse-image identification. Only the dependency's
`lean` record is changed, with the reason in `lean.note`. All definitions have real data.

`lem-kun-0f14b`: `Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections` states the
previously unstated prerequisite in the same delivery, as the human's 2026-10-16
instruction requires. Its conclusion is `IsIso` of the canonical global-sections
map for arbitrary unbounded E,K with one proper and one finite-type factor, at
exactly ℤ/nℤ coefficients. It has a source/blueprint docstring reproducing each
of its three DAG proof steps. Its only proof is `sorry`; no arbitrary isomorphism
is selected. Only the dependency's `lean` field changes.

## Prior review and return

The earlier second reader corrected the field, scheme, coefficient and Leray
hypotheses but left the Künneth maps as arbitrary invertible arguments. The
maintainer's independent review correctly found this false on the identity square
over ℤ/3 (H3). The present repair removes those arguments completely. This section
records the earlier reading's limitation and does not claim an independent reading
of the new repair; the dispatcher's fresh second reader must review these files.

## Validation

All three delivery modules compiled cleanly together through `scompile.py Q32
lem-kun-bc-kunneth-compat`, separately in dependency order, including the sandbox
and library-name checks. There were no errors or warnings. Each compiler invocation
kept the prescribed 60-second limit; wrapper elapsed times include slot acquisition.
The node copies differ from the shared base only in `lean`, every recorded signature
is verbatim from its module, and all delivered Lean lines fit within 100 characters.

Delivery-branch check: the server branch `deliver/N5/lem-kun-0f14b` at
`3935b6ab1f5a4c309ebc36d7cd7ff34896e17547` was inspected read-only. It contains only
the stage-1 node refinement and report, no Lean module or `lean` record. No
`def-kun-kunneth-map` delivery branch was listed. Thus neither provides a competing
usable Lean prerequisite; the upstream general-base map remains the one reused here.

## Second reading by Q32

Independent second reading of the repaired statement, the three delivery modules, and
all three node copies. This reading concerns the concrete-map repair described above,
not the earlier arbitrary-isomorphism version. No natural-language statement changes
or new nodes were needed. The following list was made from the node before checking
its Lean signature; each verdict is for the final files.

1. **Base field.** The node introduces a separably closed field K. Lean introduces
   `{k : Type u} [Field k] [IsSepClosed k]`. I read Mathlib's `IsSepClosed` class
   (every separable polynomial splits), the standard equivalent field-theoretic
   notion, and the dependency record. Verdict: exact; algebraic closedness is not
   required.
2. **Coefficient level and ring.** The node assumes an integer n >= 1 invertible
   in K, and A = Z/nZ. Lean uses `(n : ℕ) (hn : 0 < n) [Invertible (n : k)]` and
   everywhere the ring `ULift.{u + 1} (ZMod n)`. `ULift.ringEquiv` identifies this
   ring with Z/nZ. No arbitrary coefficient ring replaces it. Verdict: exact.
3. **X, U, and their base maps.** Lean's `aX`, `aU` have target `Spec (.of k)`;
   each has `LocallyOfFiniteType` and `QuasiCompact`. I read those Mathlib classes:
   together they are precisely finite type. There is no separatedness,
   smoothness, or independently imposed Noetherian assumption. Verdict: exact.
4. **Y projective.** Lean's `aY` has `IsHProjective`. I read the recorded upstream
   class: a closed immersion into projective space with finite coordinate type,
   with the required factorization. This is the node's finite-projective-space
   embedding convention, not relative Proj with an arbitrary graded algebra.
   Empty coordinates only give the empty source, which also embeds in P^0.
   Verdict: exact, including empty Y.
5. **Open immersion over K.** Lean uses `(j : U ⟶ X) [IsOpenImmersion j]` and
   `hj : aU = j ≫ aX`. I read Mathlib's open-immersion abbreviation and its
   dependency record. The equality is exactly compatibility with the chosen
   structure maps. Verdict: exact; no quasi-compact-open hypothesis is added.
6. **Products and all projections.** `hz : IsPullback q r aX aY` and
   `hw : IsPullback p s aU aY` supply Z and W and their projections, in reversed
   factor order relative to the printed names Y × X and Y × U. I read
   `IsPullback`: its commutative square and limit cone give exactly these fibre
   products, canonically isomorphic to the chosen products of the dependency.
   No special presentation of either product is assumed. Verdict: exact.
7. **Product morphism h.** `hq : p ≫ j = h ≫ q` and `hr : h ≫ r = s` give its
   two projections. Together with the product universal property these specify
   exactly 1_Y × j. They also make the exchange square cartesian; no additional
   cartesianness assumption is needed. Verdict: exact.
8. **Sheaf and its degree.** `F : Sheaf U.smallEtaleTopology
   (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))` is an arbitrary A-module sheaf.
   Every appearance in the formula uses `(DerivedCategory.singleFunctor _ 0).obj F`.
   I read `DerivedCategoryModule` in the coefficient module and the recorded
   derived-category module: they are this same unbounded category, not the
   bounded-below or constructible category. Verdict: exact.
9. **E, tensor, and canonical Künneth maps.** There is no free E: the helper uses
   `constantComplex Λ Y`, whose upstream definition is the derived tensor unit,
   the constant coefficient sheaf in degree zero. `kunnethGlobalSectionsMap`
   applies the existing general-base `kunnethMap` between inverse Leray and Leray
   comparisons and the tensor comparison at Spec k. Its target uses precisely
   the recorded `derivedTensor`. `constantKunnethGlobalSectionsMap` then applies
   `leftDerivedUpperStarUnitIso`, `derivedTensorLeftUnitor`, and
   `leftDerivedUpperStarIsoMapDerivedCategory`. Thus its arguments `(r,q,aY,aX,hz.w)`
   and `(s,p,aY,aU,hw.w)` give exactly k_Z and k_W, with exact inverse image in the
   targets. Verdict: exact canonical maps, not independently chosen isomorphisms.
10. **Exchange.** I read `exactDerivedSquareUpperStarIso` and
    `exactDerivedBaseChangeMap` in the recorded dependency. The first descends the
    sheaf composition square termwise; the second takes its mate under the exact
    inverse-image/derived-direct-image adjunctions. Applying it to `CommSq.mk hq`
    and the degree-zero F gives exactly q^{-1}Rj_*F → Rh_*p^{-1}F. Verdict: exact,
    without boundedness or an assumed base-change isomorphism.
11. **Leray maps.** I read the upstream definition of
    `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`: it is
    `Functor.rightDerivedFunctorCompIso'` applied to ordinary direct-image/global-
    sections composition, using preservation of K-injectives. Its `.hom.app` for
    j goes RΓ(X,Rj_*F) → RΓ(U,F), and for h goes
    RΓ(Z,Rh_*p^{-1}F) → RΓ(W,p^{-1}F). On K-injective representatives the maps are
    ordinary composition, so they are precisely the inverses of the node's
    normalized pushforward-composition comparisons. Verdict: correct directions
    and composite-adjunction normalization, not just matching endpoints.
12. **Conclusion.** Lean composes k_Z, RΓ_Z(Ex), and lambda_h on the left. On the
    right it composes `tensorHom (𝟙 _) lambda_j` with k_W. This is the displayed
    equality with Lean's left-to-right composition convention. Invertibility of
    the Künneth maps is provided by the proper-factor prerequisite plus the
    constant/unit isomorphisms; the Leray comparisons are explicit isomorphisms.
    Conjugating therefore gives exactly the stated equivalent identity. There
    is no additional conclusion to assert as an independent conjunct. Verdict:
    every clause is present with the same quantifiers.

**Mismatches found and repaired.** The main theorem had two extra instance
binders. `HasSmallSiteSheafify` for this concrete module category is supplied by
library instances, not an independent hypothesis; I removed the explicit binder.
`HasInvertibleExponent` was also assumed explicitly even though none of the maps
in this equality needs it; I removed it and its redundant direct import. The
node's actual `hn` and `[Invertible (n : k)]` assumptions remain. The dependency
modules and main module omitted imports of several already-stated proof nodes;
I added those imports, using non-public imports for proof-only prerequisites.
I added the multi-definition module's missing main-definitions list. Finally,
I explained in the repaired definition node's `lean.note` that the arbitrary-base,
arbitrary-commutative-ring `AlgebraicGeometry.Etale.kunnethMap` remains publicly
imported unchanged; the three locally recorded helpers only supply its canonical
module-valued global-sections interface. I regenerated
all recorded signatures verbatim from the files. No map formula needed repair.

**Dependency reading (H4, H12, H13).** There are no new definition nodes. I read
`def-kun-kunneth-map` in full and the current server source of
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`, obtained through
`scompile.py --source`. It agrees with the shared source apart from final
whitespace. Its adjoint is the monoidality/composition/two-counit composite of
Stacks 0F1E. The local `pointGlobalSectionsTensorIso` is also real data: if F is
the derived constant functor and R is derived sections at Spec k, its `e` is
FRT → T via the exact-sections comparison and equivalence counit; its `e'` is
RFN → N via that comparison and inverse equivalence unit. Conjugating the
existing canonical derived tensor comparison by these isomorphisms yields the
correct tensor comparison RC ⊗ RD → R(C ⊗ D). The upstream monoidal-equivalence
source characterizes the comparison on K-flat representatives. No arbitrary
`Nonempty` isomorphism, scalar normalization, or hollow definition is used.
The general base definition remains available through the owning module.

I separately read the `lem-kun-0f14b` node, all three proof steps and its delivered
module. The binders give exactly a proper first factor, finite-type second factor,
separably closed base, the node's positive invertible n, any product cone, and
arbitrary unbounded E and K. Its conclusion is `IsIso` of the canonical map,
not existence of some isomorphism. The upstream `OrdinaryProper` theorem was
also opened: it concludes only `Nonempty` of an isomorphism and does not fix
this map, so it cannot replace the delivered assertion. The delivered docstring
carries each of the node's three proof steps. I checked the signatures of its
projection-formula, proper-base-change, constant-projection, symmetry and Leray
prerequisites. The canonical comparisons used in the item also agree with the
recorded pullback-of-constants, tensor-unit and inverse-image-monoidality nodes.

**Source reading.** The local literature payload is not present in this read-only
clone. I read the Stacks primary pages for 0F1E, 0F14 and 0DV0, then fetched the
upstream `etale-cohomology.tex` and `sites-cohomology.tex` into this sandbox's
scratchpad. I read `remark-define-kunneth-map`, `lemma-kunneth-one-proper`, and
`lemma-derived-pushforward-composition`, including their surrounding assumptions
and proofs. This also resolved the 503 from the 0D6E web page. The source's
proper-factor formula is unbounded in part (2), without constructibility or
separatedness of the second factor. The node retains its explicitly stated
invertibility hypothesis; no additional such hypothesis was inferred from Stacks.
The normalized composition and pasted-counit directions agree with 0DV0.

**Edge cases.** n = 0 is excluded exactly by the node, while n = 1 (the zero
coefficient ring), the zero sheaf, empty X/U/Y and the resulting empty products
are all admitted. No `Nonempty` or nonzero-ring assumption occurs. The identity
open immersion and identity square use the same fixed canonical map construction
on both sides; independent rescaling of k_Z and k_W is impossible. F can be
nonconstructible and Rj_*F can be unbounded. The statement has no index family;
empty products of finite field extensions occur only in the cited point proof
and are allowed by its finite-index formulation. The universe u is arbitrary;
Scheme.{u}, lifted coefficients and modules at u+1, and derived categories at
u+2 follow the recorded size convention. No equality between site object and
morphism universes has been imposed. All universes and variables are bound;
the helper's Λ and k are bound by its `variable` declaration.

**Independent searches.** I ran `msearch.py` with a new LeanFinder query,
"canonical Kunneth base change compatibility": eight ordinary tensor/base-change
hits, none a derived étale comparison. Loogle `CategoryTheory.mateEquiv,
"counit"` found the two generic mate-counit identities only. The grep query
`externalProduct|cupProduct` in CategoryTheory found ordinary external products
of diagrams. LeanSearch "Etale cohomology external cup product compatibility
with derived base change for an open immersion" returned eight open-immersion
and étale ring-map facts, with no match. I also ran `rg` for cup/external products,
Künneth/composition/base-change names, and all three helper names over Mathlib,
the slopmaster2 project, shared Sheaf modules, and the current shared upstream
framework. I opened `Kunneth.Ordinary`, `Kunneth.OrdinaryProper`, the cup-product
coherence results, the constant-point equivalence and the derived monoidal
comparison. Existing external-product existence isomorphisms and generic cup-
product naturality do not state this equality. No duplicate full statement or
usable pre-existing canonical module-valued helper was found.

**Stage-2 conventions.** Both delivered theorem proofs are `sorry`; the three
helper definitions have explicit data and contain no `sorry`. Their source and
owning blueprint markers are present. The main statement docstring carries all
six proof steps, including the two normalized counit formulas, representative
coherence calculation, double transpose, and final conjugation. No private
notion, file-local notation or instance, hidden statement `let`, extra axiom,
or target-unit change is present. Every Lean line is at most 100 characters.

**Validation repair.** All three final modules compiled cleanly through the dry
run's `scompile.py` path, including the added proof imports. Its first preflight
rejected only an extra `lean.declarations` entry for the imported upstream
`kunnethMap`: the name index did not recognize it, despite the live source read
above. I removed that extra entry, leaving the three locally declared helpers
listed and the full general-base public import and explanatory `lean.note`
unchanged. This is a record-only repair; no mathematical map or signature changed.

**Final validation.** `deliver2.py Q32 lem-kun-bc-kunneth-compat --no-push`
printed OK: all three final modules compile without errors or warnings and the
server stage-2 preflight passes. The dry-run commit was `13e9d89d4b`. Every node
copy changes only `lean`; recorded signatures and line widths were checked again.
