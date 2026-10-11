## Worker report

Module `Sheaf.AlgebraicGeometry.GmPicardPullback` states
`AlgebraicGeometry.Scheme.picard_cohomology_pullback`, with its sole proof `sorry`.
No definition, new node, dependency module, or statement correction is needed.

Hypothesis and clause correspondence:

- The two algebraically closed base fields are `(k k' : Type u)` with separate
  `[Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']`. No equality or algebra
  structure between them is assumed.
- The curves are `(X Y : Scheme.{u})`, with their respective `Over` instances and
  `IsCurve` instances on the structure morphisms. `IsCurve` means separated,
  finite type, dimension at most one. Smoothness, properness, connectedness and
  nonemptiness are not assumed.
- The arbitrary scheme morphism is `(u : Y ⟶ X)`, without any condition that it
  be over either base field.
- The specified adjoint comparison `c_u` is the existing
  `upperStarGmSheafToGmSheaf u`: its definition is the adjoint under
  `Etale.upperStarLowerStarAdjunction` of `gmSheafToLowerStarGmSheaf u`,
  whose components pull back units along base-change projections.
- The specified cohomology pullback is `Etale.cohomologyMap u X.gmSheaf n`.
  Its composite with `H^n(c_u)` is written
  `Sheaf.H.map (upperStarGmSheafToGmSheaf u) n (Etale.cohomologyMap ... n ...)`.
- The degree-one clause quantifies over every `(L : X.Modules) [L.IsInvertible]`.
  `Pic.ofIsInvertible L` is its class and `Pic.toCohomologicalPicardGroup X`
  is exactly the recorded canonical equivalence. The right side is the same
  equivalence for Y applied to the class of `(Modules.tensorPullback u).obj L`.
  An existential witness `h` supplies invertibility of that module as part of
  the conclusion, solely to type its Picard class. There is no assumption of
  pullback invertibility. Proof irrelevance makes the resulting class independent
  of `h`; every Picard class has an invertible module representative, so this is
  precisely the stated equality of maps on Picard classes.
- The equivalent torsor-class formulation is already contained in this equality:
  the definition of `Pic.toCohomologicalPicardGroup` is the composite of
  `picEquivQuotientTorsorGmSheaf` and `Sheaf.Torsor.classH1`, sending L to
  `Isom(O_X,L)`. Consequently the right side is the class of
  `Isom(O_Y,u*L)`. No arbitrary choice of an H1/Picard bijection is used.
- The degree-zero clause quantifies over every global unit `a : Γ(X, ⊤)ˣ`.
  `Sheaf.H.equiv₀` at `MorphismProperty.Over.mkIdTerminal @Etale X` (and Y)
  is the canonical H0/global-sections equivalence. At that final object the
  Gm sheaf is `ULift (Additive Γ(X, ⊤)ˣ)`. Thus the `ULift.up` and
  `Additive.ofMul` terms only express the existing additive universe-lifted
  encoding of units. Its right side is `Units.map u.appTop.hom.toMonoidHom a`,
  literally the pullback on global units, in that same encoding.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (available through the imports).
- `Sheaf.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`.
- `WeilConjectures.AlgebraicGeometry.Sites.Gm`:
  `Scheme.gmSheaf`, `Scheme.CohomologicalPicardGroup`,
  `Scheme.gmSheafToLowerStarGmSheaf`, `Scheme.upperStarGmSheafToGmSheaf`.
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`:
  `Scheme.Pic.toCohomologicalPicardGroup`; this imports Picard.Group's
  `Scheme.Pic.ofIsInvertible` and the torsor classification used by the equivalence.
- `WeilConjectures.CategoryTheory.Sites.Torsor`:
  `CategoryTheory.Sheaf.nonempty_equiv_H_one_torsor` and the named canonical
  `Sheaf.Torsor.classH1` (used in the existing Picard equivalence).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `upperStarLowerStarAdjunction`
  (used by the existing comparison map).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `AlgebraicGeometry.Etale.cohomologyMap`.
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero`:
  `AlgebraicGeometry.Etale.cohomologyMap_zero_eq_globalSectionsUpperStarMap`.
  Its H0 identification is `CategoryTheory.Sheaf.H.equiv₀` from
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.

Record-location observation: lem-sc-h1-gm-pic lists the right canonical equivalence
names, but its module field points to Gm, which defines only the cohomological
Picard carrier. The equivalence declarations themselves are in upstream GmPicard;
this module imports that actual location and uses the recorded declaration name.
No notion is restated. The recorded line for the torsor theorem is likewise stale;
the full signature and docstring were read at its actual location (line 1062).

Source checked: [Stacks Tag 040E](https://stacks.math.columbia.edu/tag/040E),
Lemma 21.6.1, including its proof constructing the torsor of local generators.
The node's four proof steps are carried into the declaration docstring: torsor
representation, equivariant generator pullback and contracted product, torsor/H1
functoriality, and the degree-zero identification. The local literature file
named by the node is absent on this machine, so the source was read on Stacks.

Edge cases checked before writing: empty schemes (dimension bottom satisfies
`IsCurve`), disconnected curves and zero-dimensional components remain admitted;
no characteristic restriction; the identity map and the trivial invertible module;
morphisms between curves with different base fields; degree zero uses actual
units rather than all functions. The tensor pullback is used even for non-etale
maps, for which the Gm comparison is not generally an isomorphism. No such
isomorphism is assumed. A common arbitrary universe u is used for schemes and
base fields, as in the recorded declarations; the existing Gm coefficients
live in u+1. There is no independent smaller universe of test objects.

Searches (executed through msearch.py, recorded in searches.jsonl):

- LeanFinder: "The identification of etale H1 of G_m with Picard is natural
  under pullback of schemes" returned eight hits on sheaf-module pullback,
  finite scalar extensions and ring Picard maps, none the statement.
- Loogle: `AlgebraicGeometry.Scheme.Pic, CategoryTheory.Sheaf.H` returned
  no hits (unknown identifier AlgebraicGeometry.Scheme.Pic).
- LeanSearch: "Picard group etale cohomology H1 units pullback naturality"
  was unavailable (Internal Server Error); no mathematical verdict inferred.
- Mathlib grep: `Picard|toH1Units|CohomologicalPicard` in AlgebraicGeometry
  found three comments in EllipticCurve/Weierstrass, no declaration.
- Source and project rg: `lem-sc-h1-gm-pic-pullback|toH1Units|CohomologicalPicard|
  Gm.*[Pp]ullback|[Pp]ullback.*Gm` found the canonical equivalence in GmPicard
  and unrelated Kummer/Picard applications; only dual-number Zariski analogues
  in Picard/DualNumbers, not this general etale compatibility.
- Source grep for the exact node id found no declaration.
- `tools/lean_names_upstream.py show lem-sc-h1-gm-pic-pullback` returned the
  name-index summary, no matching declaration. Exact-name rg for the proposed
  `picard_cohomology_pullback` in Mathlib, source, project and name index had
  no hits.

Validation: server scompile.py compiled the final module with exit code 0 and
no warnings. Explicit binders and `set_option autoImplicit false` prevent
unbound implicit variables. The sole theorem proof is `sorry` as required.
No statement dispute or correction.

## Second reading by V1

The node introduces the following data, checked against
`AlgebraicGeometry.Scheme.picard_cohomology_pullback` in
`lean/Sheaf/AlgebraicGeometry/GmPicardPullback.lean`:

1. Algebraically closed fields `k k'`, rendered as `(k k' : Type u)` with
   `[Field] [IsAlgClosed]`: present, with the common universe convention used
   by the surrounding scheme declarations.
2. Curves `X` and `Y` over `Spec k` and `Spec k'`, rendered by
   `[X.Over (Spec (.of k))]`, `[Y.Over (Spec (.of k'))]` and the two
   `[IsCurve]` instances: present; no smoothness, properness, connectedness,
   or characteristic assumption was added.
3. A scheme morphism `u : Y ⟶ X`: present and unrestricted, as in the node.
4. The comparison map `c_u` adjoint to pullback of units: rendered by the
   existing `upperStarGmSheafToGmSheaf u`; this is the recorded canonical
   declaration, not a private replacement.
5. The degree-one conclusion: for every invertible `L`, the composite
   `Sheaf.H.map ... (Etale.cohomologyMap ... 1 ...)` equals the canonical
   Picard class of `Modules.tensorPullback u` applied to `L`. The existential
   witness supplies exactly the pullback invertibility instance needed by
   `Pic.ofIsInvertible`; verdict: exact. This equality is the formal rendering
   of the node's equivalent torsor-class clause because the canonical Picard
   equivalence is defined by the `Isom(O,L)` torsor.
6. The degree-zero conclusion: for every unit `a : Γ(X, ⊤)ˣ`, the two
   `Sheaf.H.equiv₀` transports of the composite at degree zero equal
   `ULift.up (Additive.ofMul (Units.map u.appTop.hom.toMonoidHom a))`:
   present and exactly the global-unit pullback claimed by the node.

Edge cases checked: identity and arbitrary (including non-étale) `u`, trivial
invertible module, zero-dimensional or empty schemes admitted by `IsCurve`,
empty indexing does not arise, no `n` parameter or characteristic restriction,
and units rather than all global functions in degree zero. The statement does
not assume pullback invertibility; it quantifies the witness needed to type its
Picard class.

Searches were rerun over Mathlib, `WeilConjectures/`, and project `lean/Sheaf`
for Picard/H¹(Gₘ) pullback, `picard_cohomology_pullback`, and related torsor
terms; no existing declaration states this result. The source was checked at
Stacks Tag 040E (Lemma 21.6.1). No mismatch was found and no source or node
change was necessary. `scompile.py` compiled the module with exit code 0 and
no warnings other than the permitted theorem `sorry`.
