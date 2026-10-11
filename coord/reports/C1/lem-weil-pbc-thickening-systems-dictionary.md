## Worker report

The delivery states `AlgebraicGeometry.thickeningSystems_dictionary` in
`lean/Sheaf/AlgebraicGeometry/ThickeningSystemsDictionary.lean`, with a single `sorry` proof.
It adds the category definition in `CoherentThickeningSystem.lean`. Every theorem there
also has only `sorry`; all structure and functor data are explicit. Its four elementary
laws are named theorems, rather than embedded proof holes in definitions.

The geometric abbreviations in the item module are applications of existing constructions,
not independent definitions of base change or extended ideals: `adicThickening` is
`Limits.pullback`, `adicThickeningι` is `pullback.fst`, and `adicExtendedIdeal` is the
recorded `IdealSheafData.comap` applied to the ideal on the affine spectrum.

Hypotheses and objects:

- `A : Type v`, `[CommRing A]`, `[IsNoetherianRing A]` give exactly the Noetherian ring.
  `I : Ideal A` is unrestricted. There is no completeness assumption.
- `f : X ⟶ Spec (CommRingCat.of A)` gives the stated structure map to S.
  `[LocallyOfFiniteType f] [QuasiCompact f]` give finite type. There is no separatedness
  assumption: neither completeness nor separatedness is needed for this dictionary,
  although Remark 088F uses both when it subsequently applies the existence theorem.
- `adicThickening f I n` is X_n = X ×_S Spec(A/I^(n+1)), including n=0.
  `adicThickeningι f I n` is j_n. The binders `i`, `hi`, `hi₂` specify the canonical i_n
  by its two projections. The second projection is induced by the quotient factor map
  A/I^(n+2) → A/I^(n+1). These are specifications of the named canonical maps, not an
  extra condition on A, I, or f; the pullback property uniquely determines i_n.
  These maps are the base changes of closed immersions of quotient spectra.
- `adicExtendedIdeal f I` is precisely I O_X: transport I across Γ(Spec A) ≅ A,
  take `ofIdealTop`, then apply the recorded extended-ideal construction `comap f`.
- `ai` and `aj` choose the recorded tensor-pullback/pushforward adjunctions for i_n
  and j_n. Their existence is `Scheme.Modules.nonempty_tensorPullbackAdjunction`.
  Their explicit presence makes “adjoint to φ” and “canonical comparison” unambiguous.
  The statement is valid for any such choices, and its unit equations give the
  comparisons for those choices. No new mathematical restriction is imposed.

Clauses:

1. `∃ hX : IsNoetherian X` states that X is Noetherian. It supplies, explicitly, the
   required instance parameter for `CoherentFormalModule` and `completion` inside
   the subsequent conclusion; it is a conclusion, not an additional hypothesis.
   `∀ n, IsClosedImmersion (adicThickeningι ...) ∧ (adicThickeningι ...).ker =
   adicExtendedIdeal f I ^ (n+1)` states closedness and the defining ideal of every j_n.
2. `CoherentThickeningSystem (adicThickening f I) i` is exactly Sys. Its `term`,
   `coherent`, and `comparison` fields encode F_n, coherence and φ_n. Its `Hom.app`
   and `Hom.compatibility` encode u_n and φ_n ≫ u_n = i_n^*u_(n+1) ≫ φ'_n, the
   node's compatibility in Lean's left-to-right composition order. The existential
   functor Φ has `Φ.IsEquivalence`. For each n the natural isomorphism β identifies
   its level `op n` with j_n,*F_n, on both objects and morphisms. The transition
   equation identifies its adjacent map, after these evaluations, with the pushforward
   of `(ai n).homEquiv _ _ (M.comparison n).hom`. This is exactly the map adjoint to
   φ_n. `pushforwardComp` followed by `pushforwardCongr (hi n)` supplies the canonical
   identification j_(n+1),* i_n,* = j_n,*. No arbitrary transition maps are allowed.
3. R is the restriction functor. The natural isomorphisms r identify its evaluated
   terms and arrows with j_n^* of the coherent module and its linear maps. The
   comparison equation for R specifies φ_n after these identifications as the
   canonical comparison c_n. The preceding equation for c identifies it by the
   composite-adjunction unit identity, so c is not an unspecified family of isos.
   The natural isomorphism ρ : completion ≅ R ⋙ Φ gives the comparison with F^wedge.
   Its level-n composite with β and the pushforward of r has composite with the
   quotient projection equal to the j_n adjunction unit. Thus its components are
   precisely the canonical quotient/unit isomorphisms F/I^(n+1)F ≅ j_n,*j_n^*F;
   reversing them gives the direction printed in the node. Naturality is part of ρ,
   β, and r, not just an objectwise existence assertion.
   The `Function.Bijective` clause is the map u ↦ ρ_G.hom ≫ Φ.map u ≫ ρ_F.inv
   from compatible families on restrictions to formal completed morphisms.
   The next equality says `R.map u` corresponds to `completion.map u`.
   The equivalence b between `(R.obj F ≅ M)` and `(completion.obj F ≅ Φ.obj M)`
   is specified by b(e) = ρ_F ≪≫ Φ.mapIso e. A system isomorphism e evaluates to
   the ψ_n of the node; its arrow compatibility is exactly
   c_n ≫ ψ_n = i_n^*ψ_(n+1) ≫ φ_n. Componentwise inverse families give the converse.
4. For every coherent F₀ the final pair of clauses states support equality for its
   pushforward, using the shared nonzero-stalk convention, and the equivalence of
   properness over S₀ and properness over S. On the second side the support is that
   of j_0,*F₀, which the first clause identifies with j_0(Supp F₀).
   The last clause identifies the proper-support predicate of M.term 0 with that of
   (Φ.obj M).obj.obj (op 0). Together with `Φ.IsEquivalence`, this says precisely
   that the equivalence restricts to the two full proper-support subcategories:
   full faithfulness restricts, and essential surjectivity plus the displayed iff
   and invariance under isomorphism give essential surjectivity of the restriction.
   There is no weakened one-way preservation of proper support.

Dependency declarations used, after opening their recorded signatures and docstrings:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (every ideal finitely generated).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; the shared
  `QuasiCompact` class gives the second finite-type condition.
- `def-pc-base-change` records the actual geometric base change as `Limits.pullback`,
  `pullback.fst`, `pullback.snd` (its `moduleBaseChange` declaration is the module
  base-change part of that multi-clause dependency, not a replacement for the fibre product).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`, `ofIdealTop`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `Scheme.IdealSheafData.comap`.
- `Sheaf.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback` and its
  recorded nonempty adjunction. Mathlib `Modules.pullback` is never substituted.
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`: `CoherentModules`,
  `IsCoherentFormalModule`, `CoherentFormalModule`, `formalModuleQuotientπ`, `completion`.
  The category is the same one, including the positive-level `op n` convention.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`:
  `Scheme.Modules.HasSupportProperOver`; support is the prescribed inline stalk locus.
- The new node gives `CoherentThickeningSystem`, its compatible `Hom`, its category
  instance and its evaluation functors. Nothing is copied from a dependency.

Edge cases checked before drafting: I=0 gives constant thickenings X_n≅X; I=⊤ gives
empty thickenings and zero completed modules; the zero ring is allowed and has empty
spectrum. The empty scheme and zero coherent modules are allowed (no nonempty or
nontrivial assumption). At n=0 the ideal is I^1 and the formal level is op 0, hence
level one; every adjacent transition uses quotient exponent n+1 on its target and
n+2 on its source. All schemes and coefficient rings live in the same explicitly
bound universe, all module carriers use the project's Scheme.Modules universe, and
there is no independently smaller universe of test objects or indexing schemes.

Searches (also retained in searches.jsonl):

- LeanFinder: “compatible systems of coherent sheaves on infinitesimal thickenings
  equivalent to coherent formal modules”: eight hits, on quasicoherent sheaf data,
  module categories and sheaf functors, no compatible-system category or dictionary.
- Loogle: “Scheme.Modules.tensorPullback, CategoryTheory.Functor.IsEquivalence”:
  no hits, unknown tensorPullback identifier (project declaration, not Mathlib).
- LeanSearch: “category of compatible coherent modules with pullback transition
  isomorphisms on an increasing tower of schemes”: service unavailable (Internal
  Server Error), recorded as unavailable, not as a negative search result. The new-node validator
  requires a verdict field, so it reads “unavailable; no match verdict made”.
- msearch grep: `ThickeningSystem|thickening.*system|FormalModule` in
  AlgebraicGeometry: zero hits.
- rg of Mathlib, WeilConjectures, project lean/Sheaf and dag/lean_names_upstream.json:
  no compatible-thickening-system declaration or collisions for the new names.
  Search for the exact item id in WeilConjectures returned no match.
- DAG search for “category of systems” finds the assigned dictionary only;
  fixed-space formal coherent systems are already given by their distinct dependency.
  `blueprint_refs.py search 'pullback transition isomorphisms'`: zero blueprint nodes.
  `blueprint_refs.py ancestor` gives thm-weil-pbc-finite-etale-lifting for the new node.

Source read: the local literature/coherent.tex file is absent on this machine, so
Remark 088F was opened at https://stacks.math.columbia.edu/tag/088F. The system terms
and pullback isomorphisms are precisely its conditions (1)-(2), and the proper-support
condition is (3), with the node's one-step index shift. The dictionary proof and its
more general hypotheses are written out in the assigned node's twelve proof steps.
There is no statement dispute and no correction of the assigned node.

Compilation: the two modules were compiled together with the supplied scompile.py,
against the server build. The earlier width warning was repaired; final dry-run results
are recorded below after the delivery check.

## New nodes

`def-weil-pbc-coherent-thickening-system` defines the missing Sys category on a tower
of schemes, its compatible families, componentwise category structure, and evaluation.
Source: Stacks Remark 088F. It introduces no new sheaf, coherence, or pullback notion.
The LeanFinder, unavailable LeanSearch, Mathlib grep, source/project grep, DAG and
blueprint searches above establish that there is no existing declaration or DAG node
for this dependent family category. `CoherentFormalModule` is a category of inverse
systems on one fixed scheme; it is the target of the dictionary, not the source Sys.
The new node is cited in the item's stmt_deps and has its own module and lean record.

Validation: the combined server compile is clean (3.1 seconds). `deliver2.py C1
lem-weil-pbc-thickening-systems-dictionary --no-push` printed OK: the commit compiles
and passes preflight except for the independent second reading, which the next worker
writes. Nothing was pushed; no second-reading section was authored by this worker.

## Second reading by C1

Independent review of both sandbox modules, both node copies, the recorded dependency
nodes and their declarations. I did not write either module. Verdict: the Lean renders
all four clauses of the dictionary. No mathematical mismatch was found; no Lean or node
signature was changed. This section adds the independent review and verification evidence.

Object/hypothesis/conclusion checklist (the node's statement, in order):

1. A is an arbitrary commutative Noetherian ring, I an ideal, S = Spec A:
   `{A : Type v} [CommRing A] [IsNoetherianRing A] (I : Ideal A)` and
   `Spec (CommRingCat.of A)`. Exact. In particular, no field, domain, nontriviality,
   completeness or characteristic restriction is introduced.
2. X → S is finite type: `f` with `[LocallyOfFiniteType f] [QuasiCompact f]`.
   Exact conjunction from def-weil-finite-type-morphism; separatedness is not assumed.
3. S_n = Spec(A/I^(n+1)), X_n = X ×_S S_n, j_n and canonical i_n:
   `adicThickening` unfolds to `pullback f (Spec.map ... Ideal.Quotient.mk ...)`,
   `adicThickeningι` to its first projection. `hi` and `hi₂` specify both projections
   of i_n, the second through `Ideal.Quotient.factor` for I^(n+2) ⊆ I^(n+1).
   These determine the unique canonical pullback lift. They do not allow an arbitrary
   tower map with only the first projection specified. Exact.
4. The quasi-coherent ideal IO_X: `adicExtendedIdeal` maps I by the inverse of
   `Scheme.ΓSpecIso` into Γ(Spec A), applies `ofIdealTop`, then `comap f`.
   Reading comap's actual definition as a base-changed closed-subscheme kernel confirms
   the image ideal, not the abstract tensor pullback of the ideal module. Exact.
5. Conclusion (1), X Noetherian and j_n closed with ideal (IO_X)^(n+1):
   `∃ hX : IsNoetherian X` and the following `∀ n` conjunction. hX is a conclusion,
   then an explicit instance argument of the formal category and completion. Exact.
6. Conclusion (2), Sys objects and arrows: `CoherentThickeningSystem.term`,
   `.coherent`, `.comparison`, and `Hom.app`/`.compatibility` are precisely the node's
   coherent terms, pullback isomorphisms and compatible module maps. The Hom equation
   has the node's composition order after translating mathematical right-to-left
   composition to Lean's `≫`. Exact.
7. Conclusion (2), the pushforward dictionary functor and equivalence:
   existential Φ with `Φ.IsEquivalence`; β is a natural isomorphism of evaluation
   functors, identifying each formal term (index `op n`, paper level n+1) and each
   arrow with j_n,* of the system term/arrow. The transition equation uses
   `(ai n).homEquiv _ _ (M.comparison n).hom`, then pushforwardComp and
   pushforwardCongr(hi n). Thus it specifies the adjoint transition map, not merely
   a functor with isomorphic objects. Exact up to the displayed canonical identifications.
8. Conclusion (3), coherent restriction with canonical comparisons:
   R and the natural r identify restriction on objects and arrows with tensorPullback
   along j_n. The c unit equation is the composite-adjunction unit identity; the
   next equation specifies R's comparison through r and c. `ai` and `aj` are choices
   of existing adjunctions, whose existence is the recorded
   `nonempty_tensorPullbackAdjunction`; varying choices changes the comparisons
   compatibly, not the class of rings, schemes, or systems covered. Exact.
9. Conclusion (3), natural quotient/completion isomorphism:
   `ρ : completion ≅ R ⋙ Φ`, with its level-n composite through β and pushed r,
   is identified by precomposition with `formalModuleQuotientπ ... (n+1)` as the
   j_n adjunction unit. This characterizes the quotient identification. Its inverse
   has the direction j_n,*j_n^*F ≅ F/I^(n+1)F printed in the node. Exact and natural.
10. Conclusion (3), morphism bijection, restricted u mapping to completed u, and
    compatible isomorphism families: the Function.Bijective conjugation by ρ, the
    subsequent completion.map equality, and b with `b e = ρ.app F ≪≫ Φ.mapIso e`.
    Isomorphisms of Sys correspond exactly to component isomorphisms ψ_n: evaluation
    gives one direction; the inverse component family satisfies Hom.compatibility
    and gives the inverse direction. Quantifiers cover every F, G, and system M. Exact.
11. Conclusion (4), support equality and properness equivalence:
    the F₀ clause compares the inline nonzero-stalk locus with its image under j_0,
    then `HasSupportProperOver` for X_0 → S_0 with that for X → S of j_0,*F₀.
    The preceding equality converts the latter support into j_0(Supp F₀). Exact.
12. Conclusion (4), equivalence of proper-support full subcategories:
    the last `∀ M` iff identifies Sys's term-zero predicate with the target's formal
    term at `op 0`. Together with Φ.IsEquivalence and β, this gives both preservation
    and reflection and essential surjectivity on the full subcategories. It is not
    merely a one-way properness assertion. Exact.

Source check: read the Stacks coherent.tex text fetched read-only from
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex at
remark-reformulate-existence-theorem and lemma-i-star-equivalence; also opened
https://stacks.math.columbia.edu/tag/088F and https://stacks.math.columbia.edu/tag/087T.
088F does assume completeness and separatedness for its *existence* equivalence
from coherent modules on X. This node instead states the dictionary between systems
on varying thickenings and formal systems on X, not algebraization on X. Its twelve
proof steps use the 087T closed-immersion equivalence and quotient units and do not
use either assumption. Consequently the generality in the node and Lean is justified;
adding the existence theorem's assumptions here would strengthen the hypothesis.
No statement correction or citer correction was needed.

Dependency review: opened CoherentFormalModule.lean, Coherent.lean,
TensorPullback.lean, ClosedSubsetProperOverBase.lean, BaseChangeConventions.lean,
and Mathlib's Modules.Sheaf, IdealSheaf.Basic/Functorial, FiniteType and
ClosedImmersion declarations. CoherentFormalModule is the full subcategory of
ℕᵒᵖ diagrams with coherent terms, annihilation by I^(n+1), and quotient-induced
transition isomorphisms. completion uses those same positive powers. Coherence is
finite type with finite-type kernels for all finite free maps on all opens.
HasSupportProperOver includes closedness and properness of the reduced induced
closed support. tensorPullback is the explicit inverse-image/tensor construction;
Mathlib's different module pullback was not used. Scheme.Modules is the existing
SheafOfModules carrier. ker agrees with the defining ideal for the closed immersion
in this conclusion. Every required dependency is usable; no dependency module is missing.

New-node review (H12): def-weil-pbc-coherent-thickening-system is a definition,
status split, in the item's chapter and unit, with empty proof/proof_deps, null
proof_origin/mathlib_match, none audits and the prescribed created and blueprint
records. Its statement cites exactly its stmt_deps. Its arbitrary tower is the
ambient family-category definition specializing to 088F's thickenings; it does not
claim that an arbitrary tower is a thickening. Its module implements all its fields,
compatible Hom, componentwise identity/composition, Category and evaluation. The
three named law theorems have sorry-only proofs and explanatory docstrings; all data
are explicit. There are no private copies, hollow data or hidden sorry proof fields.
The assigned item cites this new node. It is distinct from the existing fixed-space
CoherentFormalModule category.

Edge cases: ℕ is the specified index, not a possibly empty arbitrary index type;
all levels including n=0 occur. At zero the quotient is A/I^1 and target op 0 is
formal level one; adjacent powers are n+1 and n+2. For I=0 the quotient schemes are
isomorphic to X and all comparisons are isomorphisms. For I=⊤ every quotient spectrum
is empty and all formal terms must be zero. The zero ring, empty X, zero coherent
modules, arbitrary ring characteristic and nonseparated finite-type X are admitted.
The explicitly bound universe v (u in the definition module) is arbitrary, with the
same standard Scheme.Modules convention as the dependencies; there is no independent
smaller test-object universe or unbound implicit variable.

Independent searches with different wording: msearch LeanFinder query
“inverse limits of coherent sheaves on closed subschemes with cartesian transition
maps” returned affine scheme-limit and sheaf-gluing declarations, no match.
Loogle “CategoryTheory.Functor.IsEquivalence, AlgebraicGeometry.Scheme” returned
only the two affine/small étale site equivalence instances, no match.
msearch grep “cartesian.*module|module.*cartesian|compatible.*sheaves” returned
module objects in cartesian monoidal categories, a different notion. Direct rg for
cartesian modules, coherent systems and thickenings in pinned Mathlib,
WeilConjectures, and project lean/Sheaf found the existing formal-module category
and geometric thickening results, no Sys category or dictionary. DAG search for
“category of systems” and “pullback transition isomorphisms” found this item and its
Grothendieck-existence citer only. The worker's LeanSearch service failure is
accurately recorded as unavailable, not a negative result. No existing declaration
replaces this delivery or the new definition.

H5/H6/H8/H9: every named theorem is sorry-only, definitions have explicit data,
module and declaration docstrings name sources and blueprint ids, the main theorem
docstring covers all twelve proof steps, names have no Sheaf namespace prefix,
lines satisfy the 100-character convention, and no file-local notation or local
instance is used. Both node lean.statement strings were independently compared with
the raw signature spans located by stage2_delivery.declarations: verbatim equal
(the parser's statement field itself normalizes whitespace).

Verification: combined server scompile of CoherentThickeningSystem and
ThickeningSystemsDictionary completed cleanly in 2.9 seconds, exit code 0, with
no warnings. The first compile invocation used paths relative to the repository
instead of the sandbox and failed before compilation; rerunning from the sandbox
resolved that invocation error without modifying any tool or source file.

Delivery dry run: deliver2.py --no-push printed OK, commit f75a88263 passes
preflight and compiles. The independent reading is present; no failures remain.
