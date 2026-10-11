## Worker report

The module `lean/Sheaf/Algebra/Category/ModuleCat/Sheaf/ChangeOfRingsAdjunction.lean`
states `SheafOfModules.exists_changeOfRingsAdjunction`, with its proof left as `sorry`.
It uses the dependency's actual sheafified sectionwise tensor object, rather than
Mathlib's abstract pullback. No definitions, dependency modules or new nodes are added.

Hypothesis and clause correspondence:

- The topological space is `(X : Type u) [TopologicalSpace X]`; its opens site is
  `Opens.grothendieckTopology X`. There are no separation or finiteness assumptions.
- The commutative ring sheaves and their morphism are `A B : Sheaf ... CommRingCat`
  and `α : A ⟶ B`. `𝓡` forgets commutativity to the existing `RingCat` interface;
  `𝓪` is the image of `α` under that forgetful functor, without changing sections.
- The arbitrary modules are universally bound `M : SheafOfModules (𝓡 A)` and
  `N : SheafOfModules (𝓡 B)`.
- Restriction is Mathlib's `SheafOfModules.restrictScalars 𝓪`, using the action
  through the section ring map. It is not a newly supplied or hypothetical action.
- `𝓣 M` (notation for `changeOfRings α M`), from the recorded tensor dependency, is the sheafification
  of `changeOfRingsPresheaf α M`. The latter has sections
  `(ModuleCat.extendScalars (α.hom.app U).hom).obj (M.val.obj U)` and the induced
  tensor restrictions, with the B action on the first tensor factor.
- `E` bundles the change-of-rings functor; the local notation `𝓣` names its tensor objects. `h` says its objects are exactly those
  previously defined tensors. Existentially packaging this functor introduces no
  extra assumption: the natural hom correspondences of the node define its maps.
- `adj : E ⊣ restrictScalars 𝓪` supplies hom equivalences, and includes naturality
  in both modules. After transport by `eqToHom (h M)`, these are exactly the two
  hom sets of the node, not merely hom sets of an abstract left adjoint.
- The final clause specifies the correspondence on every section `m` over every
  open `U`. `CategoryTheory.toSheafify J (changeOfRingsPresheaf α M).presheaf` is
  the underlying abelian-group sheafification unit used by `changeOfRings`.
  Applying `f.val.app U` to this unit evaluated on the explicit tensor
  `1 ⊗ₜ[A(U),α(U)] m` is precisely `f(η(1 ⊗ m))`. Thus the equivalence
  is the specified correspondence, not an arbitrary bijection.
- Naturality of `adj.homEquiv` in the first variable makes the transported `E.map`
  the canonical tensor map: evaluate at `1 ⊗ m` and use B-linearity and the
  sheafification universal property. This is why no independent choice of an
  unrelated functor is permitted by the statement.

Dependency declarations read and used:

- `def-weil-sheaf-of-modules-category` is a Mathlib leaf: `SheafOfModules`,
  `SheafOfModules.Hom`, their category structure and `val`, in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`. Its lack of a `lean` record is valid;
  the `mathlib_match` supplies this exact interface.
- `def-pur-sheaf-tensor-product`: `SheafOfModules.changeOfRings`,
  `changeOfRingsPresheaf`, `changeOfRingsMap` and its named supporting theorems,
  in `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`. Read the full module,
  including the sectionwise restrictions and the sheafification formula.
- Mathlib's `SheafOfModules.restrictScalars`, in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, and
  `PresheafOfModules.sheafificationHomEquiv` and its
  `toPresheaf_map_sheafificationHomEquiv_def` formula, in
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `Mathlib.Topology.Sheaves.Sheaf` provides the topological opens/sheaf interface.
  `Mathlib.Algebra.Category.Grp.FilteredColimits` provides the abelian-group
  sheafification instances; no sheafification hypothesis is added to the theorem.

Edge cases checked mathematically before writing: empty space and empty open,
zero module on either side, zero commutative ring sheaf, identity ring morphism,
non-injective/non-surjective ring morphisms and all characteristics. No nonzero,
flatness or local surjectivity condition is needed. Universes are explicitly bound:
`u` is any common ambient universe for the space, section rings and module sections;
any given collection fits into such an ambient universe. No fixed universe or
restriction to finite/countable opens is imposed. The theorem's only proof is
`sorry`; the full three-step source proof is in its docstring.

Searches for existing statements (all performed, with real search records in
`searches.jsonl`):

- `msearch.py ... leanfinder "Sheafified sectionwise tensor extension of scalars
  left adjoint to restriction of scalars for sheaves of modules"`: eight hits,
  all sheafification equivalences/adjunctions, not the tensor change of rings.
- `msearch.py ... loogle "SheafOfModules.restrictScalars,
  PresheafOfModules.sheafificationAdjunction"`: zero hits.
- `msearch.py ... grep "changeOfRings|extendRestrictScalarsAdj|sheafificationAdjunction"
  Algebra/Category/ModuleCat`: ordinary-ring scalar adjunction and sheafification
  adjunction; no explicit tensor sheaf change-of-rings adjunction.
- `rg` of project and upstream sources for `sheafTensor|changeOfRings|change_of_rings|
  extensionOfScalars|extendScalars`: found the recorded tensor dependency and
  ordinary ring scalar extension. Later targeted search for
  `extendRestrictScalarsAdj|changeOfRingsAdjunction|changeOfRingsHomEquiv` found
  `PresheafOfModules.changeOfRingsAdjunction` (a presheaf result, not this sheaf
  result) and ordinary-ring uses. Checked `dag/lean_names_upstream.json` too.
- `grep -rn "lem-pc-module-change-of-rings-adjunction"` in the upstream Lean:
  no declaration.
- The cited local Stacks TeX is absent on this machine. Read the primary source
  online at https://stacks.math.columbia.edu/tag/008A: Lemma 6.20.2 states the
  canonical bijection and equivalently the adjunction, with proof from Tag 006R
  and sheafification. It agrees with the node.

No statement correction, disputed statement or unusable dependency was found.
Validation: the final single-file server compile passed cleanly in 2.5 seconds.
`deliver2.py G1 lem-pc-module-change-of-rings-adjunction --no-push` printed OK:
the module compiles and preflight passes except for the independent second
reading, which the second reader supplies. Nothing was pushed.

The first preflight parses the first `:=` in the theorem type as its proof delimiter.
Consequently local abbreviations are written as `local notation`, with all inputs
explicitly bound in the preceding `variable` command, rather than as `let` binders
inside the theorem type. This changes no mathematical objects or hypotheses.
The theorem elaborates with the parameters `X`, `A`, `B` and `α` from that command.


## Second reading by G1

Independently opened the item node, both statement-dependency nodes, the complete
TensorProduct module, Mathlib's SheafOfModules and restrictScalars declarations,
and the sheafification functor and hom-equivalence formula. The local Stacks TeX
was absent, so fetched the primary sheaves.tex into this item's scratchpad and
read lines 1815–1940 (the preceding assumptions, definitions, 0089 and 008A),
and lines 430–500 (the presheaf tensor definition and 006R). Also checked
https://stacks.math.columbia.edu/tag/008A. The source assumes an arbitrary
topological space and ring-sheaf morphism, with no finiteness or separation
hypothesis. The node explicitly uses commutative rings, consistently with its
tensor dependency. The statement is unchanged and has no statement_change;
there are no new nodes or dependency modules in this delivery.

Object, hypothesis and conclusion checklist, matched with the Lean:

1. Arbitrary topological space X: `(X : Type u) [TopologicalSpace X]` and
   `Opens.grothendieckTopology X`. Verdict: exact; no geometric hypotheses.
2. Sheaves of commutative rings A and B on X: the binders
   `(A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})`.
   Verdict: exact. The notation `𝓡` uses sheafCompose with forget₂ to RingCat;
   this changes the interface, retaining the section rings and restrictions.
3. Ring-sheaf morphism a: `(α : A ⟶ B)`; `𝓪` is its image under the same
   forgetful functor. Verdict: exact, without injectivity or surjectivity.
4. Arbitrary A-module sheaf M and B-module sheaf N: universally quantified
   `M : SheafOfModules.{u} (𝓡 A)` and `N : SheafOfModules.{u} (𝓡 B)`.
   The dependency leaf's structure stores a presheaf of modules whose underlying
   abelian-group presheaf is a sheaf; Hom stores the underlying module-presheaf
   morphism. Verdict: exactly the node's objects and linear morphisms.
5. Restriction through a: `restrictScalars 𝓪` in the adjunction. Opened
   Mathlib/Algebra/Category/ModuleCat/Sheaf/ChangeOfRings.lean:35: its objects
   restrict each section's scalars through α and retain the sheaf condition;
   maps are the restricted original morphisms. Verdict: exact action.
6. B tensor over A with M, including B action: `𝓣 M` is the recorded
   `SheafOfModules.changeOfRings α M`. Its dependency module forms sections
   with ModuleCat.extendScalars, restrictions characterized on pure tensors
   by restricting both factors, and then applies module sheafification at
   the identity of B. The B action is on the first factor. Verdict: exact;
   not an abstract pullback or a private tensor definition. The supporting
   choices obtain real map data from named existence theorems; no hollow def.
7. B-linear input u: `(f : (𝓣 M) ⟶ N)`. Verdict: every tensor-sheaf morphism,
   with no extra condition on f.
8. Bijection to A-linear maps M to Res N: `adj.homEquiv M N`, precomposed on
   its input with `eqToHom (h M)`. The witness h identifies E.obj M with the
   actual tensor, so this transport is an isomorphism and preserves bijectivity.
   Verdict: exact hom sets and an equivalence, not just existence of a map.
9. Specified correspondence m maps to u(1 tensor m): the final equality,
   quantified over every f, open `U : (Opens X)ᵒᵖ`, and `m : M.val.obj U`,
   evaluates f on `(η M).app U (1 ⊗ₜ[A(U),α(U)] m)`. Opened
   Presheaf/Sheafification.lean:54 and its toPresheaf_map_sheafificationHomEquiv_def:
   this η is precisely the underlying abelian-group unit of the same module
   sheafification used by changeOfRings. Verdict: exact sectionwise formula.
10. Naturality in both modules: the bundled `adj : E ⊣ restrictScalars 𝓪`.
    Verdict: exact. E and h are conclusions, not added hypotheses. After
    transporting along h, the formula fixes E's maps: naturality in M evaluated
    on the images of 1 tensor m forces the tensor map on these generators;
    B-linearity determines it on all pure tensors, and sheafification uniqueness
    determines the sheaf morphism. Thus the existential functor cannot conceal
    an unrelated morphism action. Conversely the node's natural bijections
    supply this functor and its adjunction. Quantifier order gives one E and
    one adjunction working for all M and N, as required.

Edge cases: X may be empty, and U includes the empty open. Sheaf conditions
include empty covers. Zero module sheaves on either side and the zero ring
are allowed (no Nontrivial instance). Identity, zero, noninjective and
nonsurjective ring morphisms, and every characteristic, remain included.
There is no tensor-power index n, scheme, or separate family index in this
node, so no n = 0 or family restriction is introduced. All variables and the
universe are bound explicitly. The arbitrary common ambient universe u can
contain any given space, section rings and section modules, using Lean's
cumulative universes; it is not fixed to small sets. No unmentioned
sheafification instance is a theorem hypothesis: the topological sheaf and
filtered-colimit imports supply the instances used by the dependency.

Independent searches, with query words differing from the worker's:

- msearch leanfinder: "Morphisms from the associated sheaf of B tensor over A
  with M correspond naturally to A linear maps from M, by evaluation at the
  unit tensor". Eight hits: ordinary-ring tensor-adjunction formulas,
  presheaf tensor restrictions, and free/unit sheaf hom formulas. None is the
  stated sheafified tensor change-of-rings result.
- msearch loogle: "SheafOfModules, CategoryTheory.Adjunction". Eight hits;
  opened Sheaf/PullbackContinuous.lean:53–109. pullback is an abstract chosen
  left adjoint, and PullbackConstruction.adjunction uses the abstract presheaf
  pullback. Neither gives this dependency's explicit tensor or the formula.
  The other hits are module sheafification and pushforward adjunctions.
- msearch grep: "tensor.*adj|adj.*tensor|homEquiv|changeOfRingsAdjunction" in
  Algebra/Category/ModuleCat/Sheaf. Hits include the same abstract adjunction
  and free-module equivalences, not this result.
- Independently ran rg with "tensor.*[Aa]dj|[Aa]dj.*tensor|
  exists_changeOfRingsAdjunction|changeOfRingsAdjunction" on upstream
  WeilConjectures, project lean/Sheaf and dag/lean_names_upstream.json.
  The project has PresheafOfModules.changeOfRingsAdjunction, which I opened:
  it concerns presheaves, not sheafification. Upstream tensor-hom adjunctions
  concern different objects. No existing exact statement was found.

Mismatch and repair: the opening theorem docstring said evaluation was followed
by the sheafification unit, reversing their order. Corrected it to apply the unit
first and then evaluate f. The displayed formula was already correct; no Lean
signature, node statement, dependency or mathematical content was rewritten.
The three-step proof docstring correctly records presheaf adjunction, passage
through sheafification, and composition with the section formula. Only the
named theorem is sorry; no proof was added. Imports, namespace and line widths
follow the conventions. The node's lean.statement remains verbatim the theorem
signature. Validation results are recorded below after the server checks.

## Reviewer fix (R-mca0955)

The space and ring sheaves are restated in the form of the merged presheaf version
(`lem-pc-presheaf-change-of-rings-adjunction`) and the other landed sheaf-on-space files:
`(X : TopCat.{u}) (A B : X.Sheaf CommRingCat.{u})`, with the unit tensor written over
`A.presheaf.obj U` and `B.presheaf.obj U`. Same objects (`TopCat.Sheaf C X` is
`Sheaf (Opens.grothendieckTopology X) C`); no hypothesis or clause changed. The common
universe `u` is forced: Mathlib only supplies `HasWeakSheafify` and
`WEqualsLocallyBijective` for `Opens.grothendieckTopology X` with `AddCommGrpCat` in the
space's universe (checked: `X : TopCat.{v}` with `AddCommGrpCat.{max u v}` does not synthesize),
and `changeOfRings` requires ring and module universes equal.
