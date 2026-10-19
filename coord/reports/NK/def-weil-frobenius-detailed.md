## Worker report

This is an exact-existing-declaration delivery. The item was already stated and landed
by N9 (the shared delivery log records its promotion on 2026-10-15). I read the complete
published source through `scompile.py --source Sheaf.AlgebraicGeometry.FrobeniusDetailed`
and the matching shared source at `lean/Sheaf/AlgebraicGeometry/FrobeniusDetailed.lean`.
Both contain `WeilConjectures.FiniteFieldDatum.geometricFrobenius` and the five associated
declarations in the node's Lean record. Accordingly, only the item's `lean` field changes:
`existing: true`, branch `newtargets-dag`, no `file`, and the updated group/date/note.
No new Lean module, new notion, dependency repair, proof or statement change is delivered.
The previously recorded empty-scheme correction is retained verbatim.

Hypothesis-by-hypothesis and clause-by-clause comparison:

1. The global datum is `D : WeilConjectures.FiniteFieldDatum.{u}`, from
   `Sheaf.Paper.FiniteFieldFiber`. I read its full structure and instances: `p`, `a`, `q`,
   `prime`, `exponent_pos`, `cardinality_eq`, `k₀`, `finite_base`, `card_base`, `k`,
   and the field/algebra/algebraic-closure fields. Thus p is prime, a is positive,
   q=p^a, k₀ has q elements, and D.k is the specified arbitrary fixed closure.
2. Arithmetic field Frobenius is `FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k`
   in `Mathlib.FieldTheory.Finite.Basic`. Its full signature requires a finite field
   and algebraic extension, both supplied by D; `coe_frobeniusAlgEquivOfAlgebraic`
   gives z raised to the cardinality of k₀, which is q by `D.card_base`.
   Geometric field Frobenius is
   `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k`, in
   `WeilConjectures.Mathlib.FieldTheory.Finite.Basic`, whose actual definition is
   the inverse arithmetic Frobenius. `Fintype.ofFinite D.k₀` in the existing
   definition's body supplies an enumeration and adds no mathematical hypothesis.
3. A finite-type k₀-scheme is exactly
   `Y₀ : Over (Spec (CommRingCat.of D.k₀))` with
   `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]`. These are the bundled
   scheme-over-base convention and the two recorded parts of finite type.
   `D.geometricFiber Y₀` is the recorded `Over.pullback` object along
   `Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))`; `.left` is Y and `.hom`
   is its projection to Spec k. No alternate fibre or fixed `AlgebraicClosure` type is used.
4. `D.geometricFrobenius Y₀ : Aut (D.geometricFiber Y₀).left` has hom
   `D.galoisMap Y₀.hom (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)`.
   The full `galoisMap` body uses the existing `AlgebraicGeometry.baseChangeMap`
   with `Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom))`.
   `specGaloisMap_over` supplies exactly the equation that Spec σ lies over Spec k₀.
   Reading `baseChangeMap` shows its actual data are `pullback.map` with identity
   on the model and Spec σ on the closure. This is precisely id × Spec(γ).
5. The inverse data use `D.galoisMap Y₀.hom γ.symm`; γ.symm is arithmetic Frobenius.
   `galoisMap_inverse` states both composite-identity equations and supplies the two
   `Aut` proof fields. The morphism data are explicit, rather than chosen from an
   unconstrained existence assertion.
6. `galoisMap_projections` states that the first projection is fixed and that the
   second projection is followed by `Spec.map (CommRingCat.ofHom σ.toRingHom)`.
   The first equation makes the map over k₀ and the second is the exact semilinearity
   equation over k. No universal claim of failure of k-linearity is asserted.
7. `galoisMap_affine` conjugates by `pullbackSpecIso D.k₀ A D.k` and gives Spec of
   `(Algebra.TensorProduct.map (AlgHom.id D.k₀ A) σ.toAlgHom).toRingHom`.
   This is a ⊗ b ↦ a ⊗ σ(b), and specializes to γ. An affine open of the model
   uses this affine model calculation by base-change functoriality.
8. Absolute q-Frobenius is the recorded `Scheme.iterateFrobenius` in
   `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`. Its full construction
   takes X, `D.prime`, the equation p=0 in global sections, and `D.a`. Its base
   is literally the identity; `iterateFrobenius_apply` and
   `iterateFrobenius_app_apply` state identity on points and p^a-power on sections.
   For Y, the characteristic equation is `D.model_characteristic` applied to
   `(D.geometricFiber Y₀).hom` followed by the base inclusion. This is q-power
   by `D.cardinality_eq`; no extra characteristic hypothesis is imposed.
9. Relative Frobenius is exactly `D.relativeFrobenius Y₀` in the recorded module
   `Sheaf.AlgebraicGeometry.RelativeFrobeniusGeometricFiber`. I read its complete
   definition: `Over.pullback` of the model's q-power absolute Frobenius, with
   `model_characteristic` and `model_frobenius_over` supplying its required proofs.
   `relativeFrobenius_projections` states the model q-Frobenius on the first
   projection and the unchanged second projection, so this is a k-morphism.
   `relativeFrobenius_affine` gives a ⊗ b ↦ a^q ⊗ b.
10. The three scheme endomorphisms are these separate constructions. The phrase
    "distinct ... in general" does not claim pairwise inequality on every scheme:
    they can coincide on the empty scheme, for example. The existing module docstring
    explicitly selects the geometric scheme automorphism for all blueprint operators.
    This is the node's convention and agrees with the cited Deligne (1.1.7), (1.1.14)
    descriptions in the node; the source PDF is absent from this read-only checkout,
    so I do not claim a fresh PDF reading.

Additional dependency source signatures and docstrings read:

- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`, `asOver`;
  bundled schemes over the base are `CategoryTheory.Over` objects as the contract permits.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, and contravariant composition.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: its full declarations and module
  documentation identify the scheme pullbacks and projections; its module-specific
  `Scheme.Modules.moduleBaseChange` is not confused with scheme base change.
- `WeilConjectures.AlgebraicGeometry.PicardFunctor`: full `baseChangeMap` signature
  and body, constructing `pullback.map` with identity on the model.

Edge cases checked by inspecting these actual constructions: empty schemes and empty
opens (the absolute construction uses the equation p=0 and supports zero section rings),
a=1, arbitrary fixed algebraic closures, nonreduced models, and models where the maps
coincide. No reducedness, separatedness, smoothness or nonemptiness is added. All fields
and schemes use the universe of the dependency's datum/geometric-fibre interface; there
is no new universe restriction. No node fault or STATEMENT-DISPUTED flag is introduced.
The relative dependency's existing note already explains that the naturality source tag
is 0CC7 rather than the 0CC8 printed in its prose; no repair to that node is needed here.

Searches actually made:

- `msearch.py` LeanFinder: "arithmetic and geometric Frobenius automorphism on a finite
  field scheme geometric fiber": eight hits, including
  `FiniteField.frobeniusAlgEquivOfAlgebraic` and its power formula; no full scheme bundle.
- `msearch.py` Loogle: "geometricFrobenius galoisMap Scheme pullback": unknown identifier
  `geometricFrobenius`. A subsequent valid query,
  "FiniteField.frobeniusAlgEquivOfAlgebraic", gave seven hits including the arithmetic
  field automorphism, its power formula and its iterate formula.
- `msearch.py` grep "frobenius|pullback.map", `AlgebraicGeometry`: 25 displayed hits,
  showing generic scheme pullback constructions, not the present Frobenius bundle.
- `msearch.py` LeanSearch: "geometric Frobenius automorphism of a scheme over a finite
  field acting on algebraic closure coefficients": unavailable, Internal Server Error;
  this is not absence evidence. The searches repeated with the stage-2 sandbox root
  are retained in `searches.jsonl`.
- Direct upstream `rg` for `geometricFrobenius`, `galoisMap` and the item id found the
  fixed-`AlgebraicClosure` `Scheme.Hom.geometricGaloisFrobenius` and a convention
  mention in `WeilSheaf.PoincareDuality`; neither replaces the exact arbitrary-closure
  datum interface. A search of `dag/lean_names_upstream.json` gave no item attachment.
- Direct `rg` of shared `lean/Sheaf` found the exact existing `galoisMap` and
  `geometricFrobenius` in `Sheaf.AlgebraicGeometry.FrobeniusDetailed`, matching the
  already-landed node. The complete source was independently retrieved using the
  prescribed `scompile.py --source` command, confirming that this is published source.

Validation: the six existing declarations are checked through the required `scompile.py`
wrapper using `scratchpad/ExistingChecks.lean`. The final delivery dry run also imports
the recorded module and checks every recorded declaration before preflight. Only the
node and this report belong to the delivery; the scratch probe is not a new module.

## Second reading by NK

I independently opened the sandbox node, every statement-dependency node and its
recorded source, and the complete published `Sheaf.AlgebraicGeometry.FrobeniusDetailed`
module, both in the shared tree and through `scompile.py --source`. The latter agrees
with the shared source. This delivery correctly reuses that module with `existing: true`;
it must not introduce another definition of its geometric Frobenius.

Source reading came before the Lean comparison. I downloaded the cited Deligne PDF
from [Numdam](https://www.numdam.org/item/PMIHES_1980__52__137_0.pdf) into the sandbox
scratchpad and read printed pp. 144–145 and 150–153, including (0.1), (0.7), (1.1.7),
(1.1.8), and (1.1.14). Thus this reading removes the worker report's limitation of
not having read the PDF. In (1.1.7), arithmetic Frobenius is the q-power field map
and geometric Frobenius its inverse. In (1.1.14), the model q-power morphism extended
to the closure and the geometric field action on the coefficient factor are separate
maps, as in the node. The fixed closure and scalar-extension notation come from (0.7).
Deligne's (0.1) supplies a separated Noetherian context for his sheaf theory; the node
states the underlying scheme constructions for finite-type schemes, and these
constructions require no separatedness. Finite type over a field already gives the
Noetherian condition. No sheaf, prime ell, or cohomological finiteness assertion is
being stated here, so the sheaf-theoretic convention ell != p adds no binder to this
definition of scheme morphisms.

For the absolute/relative distinction I also fetched the official Stacks
`varieties.tex` into the scratchpad and read its Frobenii section, from the paragraph
defining characteristic p through `definition-relative-frobenius`: absolute Frobenius
is identity on the space and p-power on sections (03SM); naturality is
`lemma-frobenius-endomorphism-identity` (0CC7); relative Frobenius has a twisted target
(0CC9). The node's relative q-power endomorphism is specifically the one descended
from the finite-field model, whose q-twist is identified with itself. It is not being
confused with an endomorphism of an arbitrary k-scheme without that model.

My object/hypothesis/conclusion checklist, with the actual Lean rendering, is:

1. **Global datum.** `D : WeilConjectures.FiniteFieldDatum.{u}` supplies prime `D.p`,
   `1 ≤ D.a`, `D.q = D.p ^ D.a`, the finite field `D.k₀` of cardinality `D.q`, and
   the specified closure `D.k` with `IsAlgClosure D.k₀ D.k`. I opened the structure
   in `Sheaf.Paper.FiniteFieldFiber`, including its instance attributes. Verdict: exact;
   no canonical-closure substitution or extra finiteness of the closure.
2. **Arithmetic and geometric field maps.** The recorded Mathlib dependency gives
   `FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k`; its coercion formula is
   `(· ^ Fintype.card D.k₀)`. `D.card_base` identifies this exponent with q.
   The upstream `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic` is literally its
   inverse. I read both definitions and their section variables. Algebraicity follows
   from `IsAlgClosure`; `Fintype.ofFinite` chooses only an enumeration. Verdict: exact.
3. **Model and geometric fibre.** `Y₀ : Over (Spec (CommRingCat.of D.k₀))`,
   `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]` give exactly a finite-type
   k₀-scheme. The recorded finite-type dependency uses this pair of classes; their
   Mathlib signatures were opened. `D.geometricFiber Y₀` is `Over.pullback` along
   `Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))`, with the second projection
   as structure map. The recorded `Scheme.Over`/`asOver` interface and bundled `Over`
   describe the same category. Verdict: exact, no smoothness or reducedness assumption.
4. **Coefficient base change.** `D.galoisMap Y₀.hom γ` is the existing
   `AlgebraicGeometry.baseChangeMap` applied to `Over.homMk (Spec.map γ.toRingHom)`.
   I opened its upstream body in `PicardFunctor`: it is `pullback.map` with identity
   on the model and `Spec γ` on coefficients. `specGaloisMap_over` supplies exactly
   the equation expressing that γ fixes k₀. The recorded `BaseChangeConventions`
   module expressly reuses this scheme map; its module-pullback declaration is not
   an alternative scheme construction. Verdict: exactly id × Spec(γ).
5. **Automorphism and inverse.** `D.geometricFrobenius Y₀ : Aut ...` has that actual
   hom and has `D.galoisMap Y₀.hom γ.symm` as actual inverse; `galoisMap_inverse`
   supplies both identity proofs. Since γ is inverse arithmetic Frobenius, this is
   precisely the inverse specified by the node. Verdict: exact, no existence-only choice.
6. **Over k₀ and semilinear over k.** `galoisMap_projections` has both required
   equations: its first projection is unchanged, and its second is followed by
   `Spec.map σ.toRingHom`. Together with `specGaloisMap_over` these give the k₀-map
   and the exact semilinearity square. Verdict: exact; there is no false assertion
   that the map is never a k-map on any model.
7. **Affine description.** `galoisMap_affine` conjugates using the canonical
   `pullbackSpecIso` and gives Spec of
   `(Algebra.TensorProduct.map (AlgHom.id D.k₀ A) σ.toAlgHom).toRingHom`.
   The direction of conjugation is correct: tensor spectrum to pullback by `.inv`,
   then the coefficient map, then back by `.hom`. This is a tensor b mapped to
   a tensor σ(b); affine opens of a model use the same construction by restriction.
   Verdict: exact, including nonreduced and zero coefficient algebras.
8. **Absolute q-power map.** The recorded dependency is
   `Scheme.iterateFrobenius X D.prime hX D.a` with `hX : (D.p : Γ(X, ⊤)) = 0`.
   I opened the full definition and `iterateFrobenius_apply` /
   `iterateFrobenius_app_apply`: the base is literally identity and the section map
   raises to `D.p ^ D.a = D.q`. For Y the structure map to k₀ supplies hX through
   `model_characteristic`. Verdict: exact; characteristic is derived, not assumed anew.
9. **Relative q-power map.** The recorded `D.relativeFrobenius Y₀` is the actual
   image under `Over.pullback` of the model's absolute q-power Frobenius, using
   the named `model_frobenius_over` proof. Its projection theorem fixes the k
   projection and applies q-Frobenius on the model projection; its affine theorem
   is Spec of `frobeniusAlgHom ⊗ id`, hence a tensor b mapped to a^q tensor b.
   I read the entire dependency module, including the proof docstrings. Verdict: exact.
10. **Three maps and convention.** These are three separate constructions, generally
    different; the node does not assert pairwise inequality for every model. The module
    documentation expressly selects the geometric scheme automorphism for the blueprint's
    Frobenius operators. Verdict: exact; no factorization or extra conclusion is added.

Edge cases: the empty scheme and its zero rings of sections are allowed: the absolute
map uses the equality p = 0 and `iterateFrobeniusOfPrime`, not a nontrivial-ring
`ExpChar` assumption. Empty opens and the zero affine algebra are also allowed.
The inverse and projection statements make sense for their unique maps. For the
minimal exponent a = 1 and prime p = 2 nothing changes. a = 0 is deliberately
excluded by the global datum, exactly as the node requires; the upstream absolute
iterate itself also accepts n = 0. There is no index set to restrict. Neither
separatedness, connectedness, smoothness, nor nonemptiness is a new hypothesis.
`universe u` is explicitly bound, and fields, models, affine rings and geometric
fibres use the recorded datum's universe throughout; no equation between previously
independent universes is imposed by this delivery. A common universe can hold any
given set-sized finite-type model and its fields.

The existing empty-scheme statement correction was read against the source first:
the construction in (1.1.14) still exists for an empty model and is then over every
base. Thus qualifying the non-k-linearity remark is necessary and changes no map.
I enumerated the current DAG citers: exactly 34, agreeing with every id recorded in
`statement_change.citers`. I opened two of them in full:

- `def-trf-scheme-frobenius`: holds true. It needs the geometric/arithmetic coefficient
  maps and the q-power model map, which are unchanged, including all their iterates.
- `lem-weil-frobenius-square-cartesian`: holds true. Its inverse, naturality and
  Cartesian-square clauses use the same explicit maps and remain valid on empty schemes;
  no universal failure of k-linearity is used.

Independent searches used different wording from the first worker:

- LeanFinder through `msearch.py`: "base change action of an algebra automorphism on
  the coefficient factor of a geometric fibre". Eight hits, all elliptic-curve base
  change interfaces, not this datum-indexed construction.
- Loogle through `msearch.py`: `FiniteField.frobeniusAlgHom`. Eight hits, including
  the exact q-power algebra map, its coercion and field-automorphism relatives; these
  supply the dependency's field/affine ingredients, not a second scheme bundle.
- LeanSearch through `msearch.py`: "geometric Frobenius scheme automorphism obtained
  from the inverse power map of a finite field". Service unavailable (Internal Server
  Error); this is recorded as unavailable, not as an absence result.
- Direct `rg` for coefficient action, Galois maps, and geometric Frobenius in Mathlib,
  upstream `WeilConjectures`, and shared `lean/Sheaf`. Mathlib has the field maps but
  no scheme bundle; upstream `Scheme.Hom.geometricFiberGaloisMap` and
  `geometricGaloisFrobenius` fix the closure to `AlgebraicClosure k` (I opened their
  signatures and bodies). The shared module is the exact existing arbitrary-closure
  declaration recorded here and is therefore reused. No missing notion needs a new node.

H5/H6/H8/H9 inspection: the two definitions have explicit morphism data and use named
proof theorems; none selects an arbitrary map or contains a data `sorry`. All four
helper theorem proofs in the existing module are `sorry`, with source/blueprint
docstrings and complete natural-language arguments. The node is a definition and
has no proof steps to import. The namespace, bound variables and 100-column source
layout agree with the conventions. No sibling modules or new/dependency node records
are delivered. The stored `lean.statement` matches the main definition's signature
under the project's whitespace/modifier normalization.

Mismatches found and changes: no mathematical mismatch in the first worker's existing
declaration attachment. I added this independent, clause-by-clause reading, a fresh
primary-source reading, and the explicit correction/citer check; I updated the Lean
record's date to this reading's date. The node statement, existing correction and
Lean declarations are preserved.

Validation: `scompile.py NK def-weil-frobenius-detailed scratchpad/ExistingChecks.lean`
from the sandbox passed, checking all six recorded declarations against the published
module; no warnings. The first invocation from the shared directory only failed to
locate that relative scratch path and was rerun from the correct sandbox directory.
