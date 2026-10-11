## Worker report

The item module states first-variable naturality of a specified canonical Ext/cohomology
comparison and the projective-line specialization, including the action on Cech cochains.
Every theorem proof is `sorry`. Definitions have explicit data; their postponed exactness,
evaluation-isomorphism, and bijectivity proofs are separate named theorems.

Hypothesis and clause correspondence:

- An arbitrary scheme is `{X : Scheme.{v}}`; arbitrary universes are explicitly declared.
- F and F' are objects of `X.Modules`, with `[F.IsFiniteLocallyFree]` and
  `[F'.IsFiniteLocallyFree]`. These are the existing variable-local-rank classes, not the
  constant-rank variant. G is unrestricted. The Ext size instance is `[HasExt.{v} X.Modules]`,
  the library's size witness, which exists for scheme modules (not an extra geometric assumption).
- The morphism u is `f : F' ⟶ F`; every nonnegative degree is `i : ℕ`.
- The canonical identifications are `locallyFreeExtAddEquivH F G i` and its F' counterpart.
  Their actual additive map applies the exact internal Hom functor to an extension,
  precomposes with the class of the identity section in degree zero, and applies the inverse
  of evaluation. This is the injective-resolution/derived-composite comparison in the node.
- Pullback is `(Abelian.Ext.mk₀ f).comp z (Nat.zero_add i)`, the Yoneda precomposition.
  The other side is `H.map (dualMap f ▷ G) i`, exactly H of u-dual tensor identity.
- The particular field is `k : Type v [Field k] [IsAlgClosed k]`. The scheme is the existing
  `ProjectiveLine (Spec (.of k))`, and `d : ℤ` includes negative twists.
- L is the existing `ProjectiveSpace.twist ... d`, O is `SheafOfModules.unit`, and omega is
  `(X ↘ Spec (.of k)).relativeDifferentials`, not an unrelated line bundle. The recorded
  `ProjectiveLine.nonempty_relativeDifferentials_iso_twist` from monomial (iii) supplies its
  identification with O(-2). `E : ProjectiveLine.TwistData ... d L` records the specified
  generators and gluing relation; it is coordinate data for the twists in the node.
- `s : O ⟶ L` is exactly a global section, by the existing unit/global-section equivalence.
- `unitMap` is the canonical map O-dual tensor omega to omega, using dual evaluation of O
  and the tensor unitors. `m` is u-dual tensor identity followed by this identification.
- The first conjunct of `p1_ext_pullback_cech_multiplication` says that Cech cohomology of m,
  transported by a natural Cech/sheaf-cohomology comparison, is the Ext pullback transported
  by the same specified canonical Ext comparison and the canonical unit identification.
  The comparison is a natural isomorphism on the existing full subcategory of abelian sheaves
  Cech-acyclic on affines. `hM`, `hω`, and the comparison are conclusions, not added hypotheses.
  This is the same full subcategory used in the proof of the recorded affine Cech theorem.
  A natural comparison simultaneously controls both objects, rather than choosing unrelated
  arbitrary additive equivalences for the source and target. Naturality means its choice
  cannot change the transported map.
- The second conjunct spells out multiplication on cochains. For every degree p and tuple y,
  V is the finite intersection of its cover members. On either chart containing V, g is the
  restriction of E.g0 or E.g1. The premises express `s|V = sigma * g`, the normalization
  phi(g) = 1 of the dual generator, and a component `c y = phi tensor tau`. The actual Cech
  cochain map has component `sigma • tau`. This covers both charts and the Laurent overlap,
  including repetitions in the unnormalized Cech complex. These coordinate premises specify
  the coefficient and tensor representation; they impose no restriction on s or the cochain.
  Since a dual generator trivializes L-dual on V, all components have this representation.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Modules.Ext`:
  `AlgebraicGeometry.Scheme.Modules.nonempty_ext_addEquiv_H`, with its full signature and
  docstring. Its record needs the dependency module below to expose the canonical map.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`:
  `AlgebraicGeometry.ProjectiveLine.TwistData`, including g0, g1, both local trivialization
  clauses and the gluing relation.
- `WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine`: all five declarations in
  the monomial node's record were read. The relative-differentials/twist isomorphism is used
  explicitly; the bases motivate the specialization but no basis restriction is imposed.
- Existing supporting APIs: `dualMap`, `presheafDualEvaluation`, `SheafOfModules.homFunctor`,
  `homObjSectionsEquiv`, `tensorObjIsoSheafification`, `PresheafOfModules.tensorHomCurry`,
  `Abelian.Ext.mapExactFunctor` / `Functor.mapExtAddHom`, `H.zeroLinearEquiv`, `H.map`,
  `tmulSection`, `unitSectionsEquiv`, `TopCat.Presheaf.cechComplex`, and
  `TopCat.Sheaf.cechCohomologyFunctor`. No sheaf, tensor, dual, Ext, or Cech complex is copied.

Source: the source blueprint is absent in the local literature checkout. Read the complete
`thm-sc-p1-duality.md` on the server by read-only ssh. Step 1 identifies locally free Ext
with dual-tensor cohomology and computes the monomial product; Step 2 names the natural
Yoneda pairing. The DAG's four detailed proof steps are carried in the theorem docstrings.

Edge cases checked: i=0 (ordinary precomposition/evaluation); zero F or F'; variable ranks
on disconnected schemes; the empty scheme; identity and zero u; d<0 (only the zero global
section); d=0 (constant scalar multiplication); d=1 (multiplication shifts the Laurent
basis, for s=a+bt the t^-2 class contributes b times t^-1); characteristic two (the omega
transition sign is a unit and causes no division by two). No bound on d or i, nonzero
section, reduced scheme, or characteristic hypothesis was added.

Searches performed with the required msearch tool:

- leanfinder: "Naturality of Ext cohomology for locally free sheaves precomposition is dual
  tensor map" returned eight free/unit/pullback Hom-equivalence lemmas, no requested theorem.
- loogle: "CategoryTheory.Abelian.Ext, CategoryTheory.Abelian.Ext.mk₀" returned Ext's
  degree-zero composition and functor APIs, no sheaf dual-tensor comparison naturality.
- grep: "ext.*(addEquiv|naturality)|Ext.*locally|ext_addEquiv_H" returned unrelated Mathlib
  hits, no requested theorem.
- leansearch: "canonical Ext cohomology comparison for finite locally free sheaves natural
  in first argument" failed with Internal Server Error; recorded as unavailable.
- rg in `WeilConjectures/` and `lean/Sheaf/`: Ext comparison exists only as the recorded
  nonempty theorem; no canonical comparison map or first-variable naturality declaration.
  Also searched the item id and the upstream declaration index: no exact existing statement.
- Read the full relevant Ext, Dual, sheaf InternalHom/Monoidal, cohomology Defs/Affine,
  ProjectiveLine, TransitionUnits and Cech source APIs to avoid private copies.

No statement correction, disputed statement, or new definition node was needed.

## Dependency modules

`lem-sc-ext-locally-free`: the recorded `nonempty_ext_addEquiv_H` supplies only an abstract
existence result; applying Classical.choice to that result would not produce the canonical
comparison or justify its first-variable naturality. The added module
`Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology` constructs the canonical comparison from
existing exact-functor Ext and evaluation APIs and states its bijectivity under the original
hypotheses. The first-class comparison is defined without sorry data. Named postponed
proofs are `isIso_locallyFreeEvaluation`, `locallyFreeHomAbelianFunctor_exact`, and
`bijective_locallyFreeExtComparison`, each with its source and complete proof outline.
The final declaration is `locallyFreeExtAddEquivH`. Only this dependency's `lean` field changes.

Repair of the earlier attempt: the projective-line statement now supplies the scheme-level
unit invertibility instance and passes its existing sheaf-level counterpart explicitly to
finite local freeness. The dependency module also explicitly defines
`locallyFreeUnitExtAddEquivH G i : Ext O G i ≃+ G.H i`, rendering its final "in particular"
clause using the dual-unit evaluation isomorphism and `H.mapLinearEquiv`.
The additional declaration name was searched in Mathlib, upstream, and `lean/Sheaf`, with
no hit. The repeated LeanFinder search for "Naturality of Ext cohomology for finite locally
free sheaves dual tensor precomposition" returned internal-Hom and free/unit equivalence
naturality lemmas, with no match for this node.

## Second reading by F1

I independently opened both delivered modules, both node copies, the base dependency
records, and their recorded source declarations. I read the complete source blueprint
`thm-sc-p1-duality.md` (Step 1 and the natural Yoneda pairing in Step 2) and
`lem-sc-ext-locally-free.md` over read-only ssh. These source places are blueprint Markdown,
not Stacks tags with a surrounding .tex context. The general comparison assumes an
arbitrary scheme and finite locally free first argument; the projective-line application
assumes an algebraically closed field. No Noetherian, connectedness, positive rank,
nonzero section, or characteristic restriction is implicit in the relevant source.

The statement inventory and its Lean rendering are as follows. Each verdict is pass.

| Node object, hypothesis, or conclusion | Lean rendering and verdict |
| --- | --- |
| Arbitrary scheme X | `{X : Scheme.{v}}`, with an explicitly bound arbitrary universe; pass. |
| Finite locally free F and F' | `(F F' G : X.Modules)` and the two `IsFiniteLocallyFree` instances; pass. I read the class at LocallyFree.lean:156: finite ranks vary over the cover, so this does not impose constant rank. |
| Arbitrary O_X-module G | The third object binder has no coherence or local freeness instance; pass. |
| Morphism u from F' to F | `(f : F' ⟶ F)`; pass, including its contravariant direction. |
| Every nonnegative cohomological degree | `(i : ℕ)`; pass, including zero. |
| Canonical Ext/cohomology identifications for both first arguments | `locallyFreeExtAddEquivH F G i` and `locallyFreeExtAddEquivH F' G i`; pass, with actual canonical map data rather than a choice of an arbitrary equivalence. |
| Pullback of each extension | For every `(z : Ext F G i)`, `(Abelian.Ext.mk₀ f).comp z (Nat.zero_add i)`; pass. I checked `Ext.comp` takes Ext(F',F,0) followed by Ext(F,G,i). |
| Induced cohomology map of u-dual tensor identity | `H.map (dualMap f ▷ G) i`; equality with the transported pullback is the entire general theorem conclusion; pass. |
| Algebraically closed field and projective line | `(k : Type v) [Field k] [IsAlgClosed k]` and `ProjectiveLine (Spec (.of k))`; pass. |
| Every twist O(d), first argument O, and canonical sheaf omega | `(d : ℤ)`, `ProjectiveSpace.twist ... d`, `SheafOfModules.unit`, and the relative differentials of `X ↘ Spec (.of k)`; pass. The monomial (iii) declaration really identifies these relative differentials with twist -2. |
| Global section s | `(s : O ⟶ L)`; pass by the existing unit/global-section correspondence. `E : ProjectiveLine.TwistData ... d L` supplies exactly the generators and gluing stipulated by def-sc-p1-standard, not a further geometric condition. |
| Ext degree-one pullback lands in H1(omega) | The first conjunct quantifies all `z : Ext L ω 1`, with `mk₀ s` followed by the canonical O comparison and `H.map unitMap 1`; pass. `unitMap` is evaluation of the dual of O and the tensor unitors, exactly the last clause of lem-sc-ext-locally-free. |
| The same pullback is induced by multiplication on Cech cochains | `m := (dualMap s ▷ ω) ≫ unitMap`; the first conjunct transports the actual Cech cohomology map by one natural isomorphism `e`, and the second conjunct identifies its component with `σ • τ`; pass. |
| Standard charts and their Laurent overlap | `U := ProjectiveSpace.standardOpen ...`, `V := ⨅ l, U (y l)`, and the restrictions of `E.g₀` or `E.g₁`; pass. This includes repeated indices in the unnormalized complex. |
| Local meaning of multiplication by s | Premises `s.app V ... = σ • g`, `φ(g) = 1`, and `c y = tmulSection φ τ`, followed by component equality to `σ • τ`; pass. TwistData's bijective scalar-generator fields make these coordinate descriptions available for every component. A rank-one dual makes every tensor section of this form, so the formula does not omit nonsimple components. |

Dependency-module review (H13): the old `nonempty_ext_addEquiv_H` states only existence
of an additive equivalence and cannot name the canonical comparison used in the item.
The delivered dependency retains exactly the scheme, variable-rank finite locally free
F, arbitrary G, and all degrees of its node. `locallyFreeEvaluation` uses the existing
internal Hom, presheaf evaluation, tensor currying and sheafification; its data contain
no sorry. Applying the exact internal-Hom/forgetful functor to Ext and precomposing with
the degree-zero identity section gives the specified comparison, followed by inverse
evaluation. This is the usual injective-resolution comparison of the node, not an
unrelated abstract bijection. `AddEquiv.ofBijective` postpones only its proof of
bijectivity, through a separately named theorem. `locallyFreeUnitExtAddEquivH` renders
the dependency's final specialization to O explicitly. The other postponed proofs are
named, sourced, and documented, and all theorem proofs remain sorry. No new definition
node or additional dependency module is missing.

I also read `dualMap`, `dualEvaluation`, `H`, `H.map`, `H.zeroLinearEquiv`, the exact-functor
Ext map API, and all five signatures recorded for lem-sc-p1-monomial. The natural
Cech comparison in the conclusion is on the existing `cechAcyclicOnAffines` full
subcategory. Affine.lean's proof of `nonempty_cechComplex_linearEquiv_H` constructs
precisely a natural isomorphism on that subcategory. The membership proofs and the
comparison are conclusions, not additional hypotheses. Its naturality makes the
transported map equal to H(m) independently of the chosen natural comparison; it cannot
conceal an arbitrary source/target change of basis. No duplicate tensor, dual, sheaf,
cohomology, or Cech notion is introduced. The HasExt size instance is supplied for every
scheme by its Grothendieck abelian category instance; it adds no geometric hypothesis.

Edge cases: the general theorem permits the empty scheme, zero modules, rank zero,
and varying ranks on disconnected schemes. It includes i=0 and identity and zero
morphisms. The special case includes d=0, d<0 and the zero section; for d=1 the Laurent
formula for s=a+bt sends the t^-2 class to b times the t^-1 class. Characteristic two is
allowed: the omega transition sign uses no inverse of 2. No general index set occurs in
the item; the Cech tuples have p+1 entries, and p=0 is included. The empty open has zero
section groups, so its coordinate formula remains valid. The universe parameters are
explicitly bound and arbitrary; ULift on Fin 2 is a size choice, not a restriction on k.

Independent searches, using queries different from the writer's:

- LeanFinder: `Yoneda composition agrees with multiplication of sections on sheaf Cech
  cohomology` returned eight nonabelian-cocycle and Mayer-Vietoris results, none matching.
- Loogle: `CategoryTheory.Abelian.Ext.comp` returned the composition and its basic
  associativity/zero/degree-zero lemmas; none states this dual-tensor comparison.
- LeanSearch: `Ext first variable contravariant dual tensor sheaf cohomology comparison`
  was unavailable (Internal Server Error), recorded by msearch; no result claimed.
- msearch grep: `Ext.*(dual|cech)|ext.*(cohomology|evaluation)` returned unrelated matches.
- Direct rg in upstream WeilConjectures and project lean/Sheaf, using
  `ext.*(cech|naturality|comparison|addequiv)|yoneda.*(multiplication|cohomology)|locallyFreeEvaluation`,
  found the recorded abstract Ext comparison and generic Cech/Ext APIs, not this theorem
  or its canonical comparison construction. I opened the relevant existing APIs rather
  than inferring their meaning from their names.

Mismatch found and repaired: the docstring of `locallyFreeHomAbelianFunctor` called it
exact although that definition has arbitrary F. Exactness is correctly stated separately
under finite local freeness. I removed the unconditional word "exact" from the docstring.
No signature, definition data, node statement, or node dependency needed alteration.
Both node `lean.statement` fields match their main signatures verbatim. The item
has no statement_change and needs none. The statement docstrings carry the evaluation,
resolution, derived naturality, local multiplication, and Cech comparison proof steps.
The modules compiled together cleanly on the server before this documentation-only repair;
the delivery dry run recompiles the final files and checks all records.
