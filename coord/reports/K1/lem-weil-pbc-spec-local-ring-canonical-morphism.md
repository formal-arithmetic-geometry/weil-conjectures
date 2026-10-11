## Worker report

The module `Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism` states the node in
four named theorems, all with `sorry` proofs. It introduces no definitions. The canonical
morphism is Mathlib's `AlgebraicGeometry.Scheme.fromSpecStalk`, not a second construction.
The node statement is unchanged. Two landed dependencies were added: the scheme-module
specialization `def-pc-module-stalk-functor` and the canonical unit
`lem-pc-module-pullback-adjunction`.

Hypotheses and clauses:

| Node text | Lean rendering |
| --- | --- |
| Arbitrary scheme Y and point y | `(Y : Scheme.{u}) (y : Y)`; explicit universe u, no finiteness, separation, or field assumptions |
| A = O_{Y,y}, Y' = Spec A, closed point m | `Y.presheaf.stalk y`, `Spec (Y.presheaf.stalk y)`, `IsLocalRing.closedPoint (Y.presheaf.stalk y)` |
| Canonical c corresponding to (y,id) | `Y.fromSpecStalk y`; its closed point equality and normalized closed stalk equality in `fromSpecStalk_local_properties` identify precisely this pair under `SpecToEquivOfLocalRing` |
| Every affine V containing y; natural R_p -> A is an isomorphism | `fromSpecStalk_affine_description`, with `V`, `hV : IsAffineOpen V`, `hy : y ∈ V`, and `e : Localization.AtPrime (hV.primeIdealOf ⟨y,hy⟩).asIdeal ≃+* Y.presheaf.stalk y`. The equation `e.toRingHom.comp (algebraMap ...) = (Y.presheaf.germ V y hy).hom` pins e to the natural localization map. Localization uniqueness ensures this is the map stated, not an arbitrary ring isomorphism. |
| c factors through Spec R_p -> Spec R = V -> Y, independent of V | `Spec.map (Y.presheaf.germ V y hy) ≫ hV.fromSpec = Y.fromSpecStalk y`. The germ map factors through the preceding natural e, so contravariant Spec gives the stated factorization. The same RHS for every V expresses independence. |
| (1) c(y') = y | First conjunct of `fromSpecStalk_local_properties` |
| (1) Image equals generalizations of y | `Set.range (Y.fromSpecStalk y) = {x : Y \| x ⤳ y}`; specializes is oriented from the generalization to y |
| (1) Every open V containing y has c^{-1}(V) = Y' | `∀ V : Y.Opens, y ∈ V → (Y.fromSpecStalk y) ⁻¹ᵁ V = ⊤`; equivalently the image is contained in V |
| (2) Every local homomorphism c_q^sharp is an isomorphism | `∀ q : Spec (Y.presheaf.stalk y), IsIso ((Y.fromSpecStalk y).stalkMap q)`; these maps are local by Scheme.Hom |
| (2) Closed stalk map is identity under O_{Y',y'} = A_m = A | `stalkClosedPointTo (Y.fromSpecStalk y) = (Y.presheaf.stalkCongr (Inseparable.of_eq fromSpecStalk_closedPoint)).hom`. The LHS is c.stalkMap y' followed by `stalkClosedPointIso A`. The RHS is the canonical transport O_{Y,c(y')} -> O_{Y,y}, thus identity after c(y') = y. |
| (3) c is flat | `Flat (Y.fromSpecStalk y)` |
| (4) Every O_Y-module G, with its recorded pullback | `(G : Y.Modules)` and `(Modules.tensorPullback (Y.fromSpecStalk y)).obj G` |
| (4) Germ map is an A-module isomorphism | `fromSpecStalk_module_stalk` asserts an isomorphism e from the original stalk to the pullback stalk with scalars restricted along c.stalkMap y'. The source is written at c(y') rather than y to avoid a dependent cast; clause (1) identifies these points. Clause (2) identifies this restriction of scalars with the A-action in the node. |
| (4) Map sends germ s to germ of unit(s) | The equation quantified over every V containing c(y') and every `s : G.val.obj (op V)` pins `e.hom` to this particular map. The unit is `Classical.choose (Modules.exists_tensorPullbackAdjunction c)`, whose unit is explicitly pinned to the canonical sectionwise tensor map. The target germ is over c^{-1}(V), equal to Y' by clause (1). |
| (4) Parenthetical tensor description | The stated isomorphism is the particular unit germ map, not an arbitrary isomorphism of carriers. The tensor description is the already-landed `Scheme.Modules.exists_tensorPullback_stalk_iso` in `Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`, read during preparation: its canonical comparison sends the unit germ to `1 ⊗ s_y` (the reversed-factor convention). It is not redeclared. The docstring gives exactly this identification and the inverse of m -> m ⊗ 1. |
| (5) Every proper ideal J | `(J : Ideal (Y.presheaf.stalk y)) (hJ : J ≠ ⊤)` |
| (5) Quotient local and quotient map local | Existential `hlocal : IsLocalRing (A ⧸ J)` and `hmap : IsLocalHom (Ideal.Quotient.mk J)`; these are conclusions, not extra hypotheses |
| (5) Morphism corresponding to (y,quotient) equals quotient spectrum followed by c | `(@SpecToEquivOfLocalRing Y (CommRingCat.of (A ⧸ J)) hlocal).symm ⟨y, ⟨CommRingCat.ofHom (Ideal.Quotient.mk J),hmap⟩⟩ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Y.fromSpecStalk y` |
| (5) Quotient spectrum map is closed immersion | `IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))` |

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: `LocallyRingedSpace.Hom`, with
  underlying continuous map, sheaf map, and local stalk-map condition; scheme stalk maps
  are `Scheme.Hom.stalkMap`.
- `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.fromSpecStalk`,
  `IsAffineOpen.fromSpecStalk`, `SpecToEquivOfLocalRing`, `Scheme.stalkClosedPointTo`,
  `stalkClosedPointIso`, `stalkClosedPointIso_inv`. Their full definitions/signatures
  and docstrings were read, including the closed-stalk identification with the germ map.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `IsAffineOpen.primeIdealOf` is the prime in the affine open.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, with the stalkwise interpretation
  `Flat.iff_flat_stalkMap` recorded by the dependency.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback` (the full
  tensor formula, not Mathlib's different `Modules.pullback`).
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`:
  `Scheme.Modules.exists_tensorPullbackAdjunction`, the canonical-unit characterization.
- `Sheaf.Algebra.Homology.ModuleStalkFunctor`: `RingedSpace.moduleStalkFunctor` for
  sheaves on ringed spaces, as required by the standing MODULE STALKS convention.
  Also read the original dependency's `PresheafOfModules.moduleStalkFunctor` in
  `Sheaf.Topology.PresheafModuleStalkFunctor`: both use Mathlib's existing stalk carrier
  and module structure; the ringed-space functor packages it over the CommRingCat stalk.

Edge cases checked: the empty scheme has no y, so its pointed assertion is vacuous;
no zero-ring stalk can occur at a scheme point (local-ring instances are nontrivial).
All schemes and modules are allowed in the explicit universe u. All primes q of A
are included, not only its closed point. V need not be affine in clause (1) or the
module germ formula. No integral, Noetherian, reduced, proper, or separated assumption
is introduced. J = 0 is included; J = top is excluded exactly as in the node, since
its quotient is the zero ring and the local-ring correspondence would not apply.
The source point c(y') in the module theorem is the same point as y, rather than a
restriction to a special case.

Searches (2026-10-11):

- `msearch.py ... leanfinder "canonical morphism spectrum stalk flat and stalk maps
  isomorphisms"`: Flat.stalkMap, Flat.iff_flat_stalkMap, Flat.of_stalkMap,
  Scheme.arrowStalkMapSpecIso, isIso_SpecMap_stakMap_localization; no whole-node match.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.fromSpecStalk"`: the existing
  construction, its affine-independence theorem, closed-point theorem, and range theorem;
  no declaration gives the complete node including its module unit map.
- `msearch.py ... grep "fromSpecStalk" AlgebraicGeometry`: confirms these existing
  Mathlib declarations and no whole-node statement.
- LeanSearch MCP query "canonical morphism spectrum local ring stalk maps are
  isomorphisms" returned HTTP 500. Repeated through `msearch.py ... leansearch
  "canonical morphism Spec stalk flat"`, also recorded UNAVAILABLE (HTTP 500).
  No negative mathematical verdict is inferred from unavailable search.
- `rg -n 'fromSpecStalk|lem-weil-pbc-spec-local-ring-canonical-morphism'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures lean/Sheaf`: upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat` already has
  `Scheme.flat_fromSpecStalk`, but it says only clause (3), not the whole statement.
  The source `WeilConjectures.Mathlib.AlgebraicGeometry.Stalk` develops generalization
  stalk maps, not this combined statement. Project sources have citers and the general
  tensor-pullback stalk comparison, no whole-node match.
- Exact declaration-name collision search with rg over Mathlib, WeilConjectures,
  lean/Sheaf, and `dag/lean_names_upstream.json`: no hits for any of the four new names.
- `tools/lean_names_upstream.py show` consulted the upstream name index.

Source checked: the local repository has no fetched stacks-project directory, so read
[01J6](https://stacks.math.columbia.edu/tag/01J6),
[02NA](https://stacks.math.columbia.edu/tag/02NA),
[01J7](https://stacks.math.columbia.edu/tag/01J7), and
[0098](https://stacks.math.columbia.edu/tag/0098) online. The node's eight proof steps are
included, apportioned among the four declaration docstrings.

Server compile: clean, exit 0, 1.9 seconds; explicit autoImplicit false; no warnings.
No node fault or statement dispute found. No new nodes or dependency replacement modules.

## Second reading by K1

Independent second reading: opened the node copy, all ten statement-dependency nodes,
the delivered module, and the dependency declaration sources. Verdict: the four
statements together render the node faithfully. No mathematical or typing mismatch
found; no Lean or node changes. This section adds the independent review evidence.

The source .tex was absent from this machine's literature directory. Read the actual
Stacks master schemes.tex, sheaves.tex and coherent.tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/ (scratchpad copies),
including the section context, 01J6, equation 02NA, 01J7, 0098 and the proof of 02OD.
01J6/02NA concern arbitrary schemes and local rings, not Noetherian schemes. The
Noetherian/proper/coherent hypotheses in 02OD belong to formal functions; its local-ring
identification and resulting flatness do not require them. 0098 assumes only a ringed
space morphism and a module sheaf. No omitted standing hypothesis was found.

Objects, hypotheses and conclusions, matched in the node's order:

| Node item | Lean rendering and verdict |
| --- | --- |
| Scheme Y and point y | Every theorem binds `(Y : Scheme.{u}) (y : Y)`. Exact; no extra assumptions. |
| Local ring A, maximal ideal, spectrum Y', closed point | `Y.presheaf.stalk y`, `Spec (Y.presheaf.stalk y)`, `closedPoint (Y.presheaf.stalk y)`. Exact; scheme stalks carry their existing local-ring instance. |
| Canonical c corresponding to (y,id) | Mathlib `Y.fromSpecStalk y`. Read its affine construction and `SpecToEquivOfLocalRing`, whose forward map is the image of the closed point and `stalkClosedPointTo`. The first and fifth conjuncts of `fromSpecStalk_local_properties` identify this precise pair after canonical point transport. Exact. |
| Every affine V containing y, prime p, natural localization isomorphism | `fromSpecStalk_affine_description` binds `V`, `hV : IsAffineOpen V`, `hy : y ∈ V`; p is `(hV.primeIdealOf ⟨y,hy⟩).asIdeal`. Its existential ring equivalence commutes with `algebraMap` and the germ ring map. Read `primeIdealOf` and `isLocalization_stalk`: this is the prime and natural map in the node. Exact, not merely an arbitrary ring isomorphism. |
| Affine factorization, independent of V | `Spec.map (Y.presheaf.germ V y hy) ≫ hV.fromSpec = Y.fromSpecStalk y`. The preceding compatibility expresses germ as localization followed by e; applying contravariant Spec gives exactly the stated three-map composite. The same RHS for every V expresses independence. Exact. |
| (1) Closed point maps to y | First conjunct of `fromSpecStalk_local_properties`. Exact. |
| (1) Image is precisely all generalizations | `Set.range ... = {x : Y \| x ⤳ y}`. Read Mathlib's `range_fromSpecStalk`; this is the correct specialization orientation. Exact. |
| (1) Any open containing y pulls back to Y' | Third conjunct quantifies over every `V : Y.Opens`, with only `y ∈ V`, and concludes preimage equals top. Exact; no affine restriction. |
| (2) Every local stalk homomorphism is an isomorphism | Fourth conjunct quantifies over every `q : Spec A` and asserts `IsIso (c.stalkMap q)`. Read `LocallyRingedSpace.Hom.prop`: localness is inherent in the scheme morphism. Exact. |
| (2) Closed stalk map is identity under A_m = A | Fifth conjunct uses `stalkClosedPointTo c = (stalkCongr (Inseparable.of_eq fromSpecStalk_closedPoint)).hom`. Read `stalkClosedPointTo` and `stalkClosedPointIso_inv`: this normalizes using the inverse germ map, and its RHS is exactly transport to the stalk at y. Exact. |
| (3) Flatness | Final conjunct `Flat c`; read `Flat.iff_flat_stalkMap`, giving the node's definition. Exact. |
| (4) Every O_Y-module and its pullback | `(G : Y.Modules)` and `Modules.tensorPullback c`. Read the landed tensor formula, ring map, and functor. Exact; no quasi-coherence hypothesis and no use of Mathlib's different module pullback. |
| (4) Germ map is an A-module isomorphism | `fromSpecStalk_module_stalk` gives an iso from `RingedSpace.moduleStalkFunctor ... (c(y'))` to the pulled-back stalk restricted along `c.stalkMap y'`. Since c(y') = y, this is G_y and its prescribed scalar action; the normalized closed stalk identity identifies this ring with A. Exact up to those canonical identifications. |
| (4) Specified map sends s_y to the germ of unit(s) | The equation for every open containing c(y') and every section pins `e.hom` to the particular unit germ map. Read `exists_tensorPullbackAdjunction`: its sectionwise formula fixes the chosen unit to the canonical tensor/inverse-image/sheafification map. Exact, not an unspecified adjunction or unspecified module isomorphism. |
| (4) Tensor stalk description | Read landed `Modules.exists_tensorPullback_stalk_iso` and its germ formula: target is extension of scalars, and unit germ maps to `1 ⊗ s_y`, the symmetric tensor convention for the node's `s_y ⊗ 1`. This existing dependency supplies the parenthetical description; it is not restated. Exact. |
| (5) Every proper ideal J, local quotient and local quotient map | `J : Ideal A`, `hJ : J ≠ ⊤`, with existential `hlocal : IsLocalRing (A ⧸ J)` and `hmap : IsLocalHom (Ideal.Quotient.mk J)`. Localness is concluded, not imposed as an extra hypothesis. Exact. |
| (5) Corresponding morphism equals quotient spectrum followed by c, a closed immersion | `fromSpecStalk_quotient_factorization` applies the existing local-ring equivalence inversely to `(y, quotient)` and equates it to `Spec.map quotient ≫ c`; its final conjunct asserts `IsClosedImmersion (Spec.map quotient)`. Exact direction and precise quotient morphism. |

Dependency review: `RingedSpace.moduleStalkFunctor` bundles Mathlib's existing module
stalk carrier and action; the presheaf-level `PresheafOfModules.moduleStalkFunctor`
uses that same carrier. The scheme/ringed-space specialization is the landed
`def-pc-module-stalk-functor`, as prescribed by STATE. All other notions use the
recorded Mathlib or landed declarations. There are no new definition nodes or
dependency replacement modules in this delivery, and no statement_change to audit.

Edge cases: an empty scheme has no point y, as in the node. A zero ring cannot be a
scheme stalk at a point because local rings are nontrivial. The zero module is allowed.
J = 0 and J = maximalIdeal are allowed, J = top is excluded exactly by properness.
All primes q are included. No characteristic, domain, reducedness, separation,
finiteness or Noetherian hypothesis occurs. No index or n parameter exists. Universe u
is explicit and arbitrary; the module, stalk and spectrum use the project's same
universe convention. All variables and universes are bound, with autoImplicit false.

Independent searches used different queries from the worker:

- LeanFinder via msearch.py: `pullback sheaf of modules stalk isomorphism local scheme
  closed point`. Eight hits, including Tilde.stalkIso_hom and closed-point germ
  identities; none states the whole node or the unit isomorphism here.
- Loogle via msearch.py: `AlgebraicGeometry.Scheme.stalkClosedPointTo`. Twelve hits;
  opened the construction, closed-stalk identity and local-ring equivalence. They
  supply individual clauses, not the full item.
- LeanSearch via msearch.py: `local scheme canonical morphism tensor pullback stalk
  unit isomorphism`. HTTP 500/service unavailable, not a negative search verdict.
- rg over upstream WeilConjectures and repository lean/Sheaf for `fromSpecStalk`,
  `stalkClosedPointTo`, and `exists_tensorPullback_stalk_iso`, and Mathlib Stalk,
  AffineScheme and Flat. Opened upstream IsAffineOpen.flat_fromSpecStalk and the
  Scheme.flat_fromSpecStalk instance, plus the landed tensor-stalk theorem. These
  are partial results; no existing declaration gives the whole node. No new notion
  or private copy is needed.

H5/H6/H8/H9 checks: the delivery contains no definitions, only four named theorems
with sorry proofs. Each docstring names its source and blueprint id, and their
proofs collectively carry all eight node steps. No file-local notation, private
notion, local instance, hidden let/show binder, or declaration-name collision was
found. Lines are at most 100 characters. Imports provide used constructions or
properties. The primary `lean.statement` was mechanically checked against the file
and is verbatim equal. Independent scompile: exit 0, 2.1 seconds, no warnings.
