## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections` states
`AlgebraicGeometry.proEtaleComparisonPullbackSections`, with its whole proof `sorry`.
Its two supporting definitions have real data: the restriction map in the section
formula and the usual section map at an etale object. No new notion, dependency
repair, statement correction, or disputed statement is needed.

The statement uses a realization of the prescribed presheaf rather than definitional
equality of its carriers. It asserts a functor `A` into pro-etale sheaves, section
bijections `e`, their compatibility with the specified restrictions and with sheaf
morphisms, and a natural isomorphism `p : nu^* ≅ A`. Consequently the presheaf with
exactly the node's values and restrictions is isomorphic to `(A.obj F).obj`, and is
itself a sheaf: transport functor laws and the sheaf condition across `e`. This
assertion is equivalent to the node's prescribed presheaf being a sheaf and its
natural comparison isomorphism; it does not replace that presheaf by sheafification.
No arbitrary restriction map is quantified over.

Hypotheses and clauses, in the order of the node:

- An arbitrary scheme is `(X : Scheme.{u})`. The set coefficients are `Type (u + 1)`,
  as in the comparison dependency, with the object universe `u+1` and morphism
  universe `u` of both small sites retained.
- The small etale site is `X.Etale` with `X.smallEtaleTopology`; the small pro-etale
  site is `X.ProEt` with `Scheme.ProEt.topology X`. No substitute site is defined.
- The geometric comparison is the left functor in `Scheme.proEtaleSiteComparison X`;
  its very adjunction supplies the unit in the final equation.
- `F : Sheaf X.smallEtaleTopology (Type (u + 1))` is precisely a set-valued sheaf.
- `Y : X.ProEt` supplies its underlying scheme `Y.left`, structural map `Y.hom`,
  and weakly etale property without an additional hypothesis.
- `((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
  (op (Scheme.Etale.mk (𝟙 Y.left)))` is exactly the displayed Gamma of the etale
  inverse image, evaluated at the identity etale object. It is the target of `e F Y`.
- For every `g : Z ⟶ Y`, the first conjunct identifies the map of `A.obj F` with
  `proEtaleComparisonSectionRestriction F g`. This definition applies the unit
  to the global section and then the inverse of `etaleSetTerminalTransport`.
  That inverse restricts to the identity object of Z and applies the canonical
  inverse-image composition comparison and the triangle equality `g.w`. Thus it
  is section pullback followed by the specified composition identification.
- The first existential makes `A.obj F` a sheaf. The equivalences `e` and the first
  conjunct give the sheaf condition for the actual prescribed presheaf, as above.
- `p` is a natural isomorphism of sheaf functors oriented from `nu^*` to `A`.
  The second conjunct specifies the action on every `ψ : F ⟶ F'` as the map of
  the recorded etale inverse-image functor, so the realization is natural in F.
- The third conjunct says `proEtaleComparisonEtaleSection F U` is bijective for
  every etale U. Its data is the etale inverse-image unit at U followed by
  restriction along the diagonal `U → U ×_X U`. This is the usual identification
  with sections of F restricted to U_et.
- The final conjunct says that evaluation of `p`, followed by `e`, sends the
  comparison adjunction unit to exactly that usual identification, section by
  section. This is the normalization specifying the canonical comparison.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`,
  `Scheme.smallEtaleTopology` (through the imported dependency closure).
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `Scheme.proEtaleDerivedCategory`; its site is the existing `Scheme.ProEt`
  and `Scheme.ProEt.topology`, used here, imported through the comparison module.
  The derived-module part of that dependency is not needed for this sets lemma.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison`, the explicit constructed sheaf adjunction.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`.
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`:
  `etaleSetInverseImageCompositionUnits`, and its existing `Scheme.etaleSetPullback`.
  The composition comparison is used through the terminal transport definition;
  its theorem determines the chosen comparison by its unit equation.
- `Sheaf.AlgebraicGeometry.EtaleSetTerminalTransport`:
  `etaleSetTerminalTransport`. Its existing owning node
  `def-weil-pbc-sets-terminal-transport` is added to `stmt_deps`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small`:
  `Scheme.isContinuous_overPullback`, available through the dependency closure
  and specialized explicitly in the definition body to elaborate the etale unit.
- Private proof imports: `Sheaf.AlgebraicGeometry.EtaleSectionsFpqcDescent`
  (`existsUnique_etaleSection_of_fpqc_cover`) and
  `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`
  (`Scheme.fpqcCover_of_smallEtaleCover`). Other already stated proof tools
  (weakly etale composition/base change, etale finite limits/localization and
  sheafification) are available from the imported upstream/dependency closure.

Source checked directly: `literature/stacks-project/proetale.tex`,
`lemma-describe-pullback-from-etale` (Tag 0GLZ), including its full adjunction
construction, and the preceding comparison paragraph (Tag 099R). The theorem
docstring expands the node's seven proof steps, including both inverse Hom-map
checks and the canonical unit normalization omitted in the source.

Edge cases checked: empty X or Y (including the empty covering), identity
arrows, arbitrary non-etale arrows between pro-etale objects, arbitrary sheaves
of sets, and non-quasi-compact/non-quasi-separated schemes. There is no
nonemptiness, quasi-compactness, separation, or finite-coefficient assumption.
The terminal object and all section units exist for empty schemes too; the
sheaf condition then forces the unique empty-object section. Universes are the
same as the recorded comparison and etale inverse image, not equated or reduced.

Searches for reuse (2026-10-15):

- `msearch.py leansearch`, query `etale to proetale inverse image sections formula`:
  unavailable, Internal Server Error; no conclusion inferred from its failure.
- `msearch.py leanfinder`, query `The inverse image from the etale to the proetale
  site evaluated on Y is global sections of the etale inverse image on Y`:
  eight hits (etale forgetful functors, topology/category instances,
  StandardEtalePair and a condensed-space comparison), none this formula.
- `msearch.py loogle`, query `"ProEt", "sheafPullback"`: zero hits.
- `msearch.py grep`, query `proetale.*(pullback|sections)|comparison.*sections`
  under Mathlib AlgebraicGeometry: zero hits.
- `rg` of the same topic in the upstream WeilConjectures and project Sheaf sources:
  existing pro-etale comparison adjunction and abelian derived-sections statements,
  but no set-valued inverse-image sections formula. Search for the item id and
  proposed declaration name in both trees: no existing declaration.
- Focused searches of the project's etale section maps found the reusable
  `etaleSetTerminalTransport`; the general section-comparison map evaluates at
  base changes of an X-object and is not the same terminal-section restriction.
  The similarly named global section maps in fpqc modules are private, and the
  public terminal section transfer there has abelian coefficients. The owning
  node and full signature/docstring of terminal transport were read before reuse.

Compilation is exclusively through `scompile.py`, one delivered file. Expected
sorry warnings are permitted; no proof of the lemma has been attempted.

## Second reading by NK

Read the node (including all seven proof steps), Stacks `proetale.tex`,
`section-comparison` (099R) and `lemma-describe-pullback-from-etale` (0GLZ),
and the delivered Lean together. The source assumes only an arbitrary scheme
and compatible choices of the two small sites. Its displayed Hom formula has
an inverse-image/direct-image typo; the node correctly uses the direct image.
No statement correction is present or needed.

Object/hypothesis/conclusion checklist, in node order:

1. Arbitrary scheme X: `(X : Scheme.{u})`, with no property instances. Exact.
2. Small etale site: `X.Etale`, `X.smallEtaleTopology`. Read their Mathlib
   declarations and the owning node: the topology is the induced small etale
   topology, not the big site. Exact.
3. Small pro-etale site: `X.ProEt`, `Scheme.ProEt.topology X`. Read the owning
   node, `ProEtaleDerivedCategory`, and Mathlib's `ProEt`, `precoverage`, and
   `topology`: objects are weakly etale maps, arrows all X-maps, and topology
   comes from pro-etale/fpqc covers. No etaleness condition on site arrows. Exact.
4. Comparison geometric morphism: `Scheme.toProEt X` and the left functor of
   `Scheme.proEtaleSiteComparison X`. Read that dependency's constructed
   adjunction and unit; they are Kan extension/sheafification and restriction,
   precisely the node's comparison, not an arbitrary left adjoint. Exact.
5. Sheaf F of sets: `Sheaf X.smallEtaleTopology (Type (u + 1))`, uniformly
   quantified in `e` and all four conjuncts. Read the `Sheaf` declaration and
   the sheaf-of-sets node. Exact.
6. Weakly etale f:Y to X: `Y : X.ProEt`, `Y.left`, `Y.hom`. Its property is
   built into the site object. The value on Y is the target of `e F Y`, namely
   `(Scheme.etaleSetPullback Y.hom).obj F` at `op (Scheme.Etale.mk (𝟙 Y.left))`.
   Read `EtaleSheaves.etaleSetPullback` and the composition-units dependency:
   this is the prescribed etale inverse image and its terminal sections. Exact.
7. Restriction along g: `g : Z ⟶ Y`, with no extra assumption. The first
   conjunct and `proEtaleComparisonSectionRestriction` prescribe exactly the
   inverse-image unit followed by `(etaleSetTerminalTransport ...).inv`.
   Read the terminal-transport node and entire declaration: the inverse reverses
   the equality/composition/terminal-object transport, giving section pullback
   and then c in the required direction. `g.w` supplies the triangle equation.
   No arbitrary map is substituted. Exact.
8. This presheaf is a sheaf: `A.obj F` is already a sheaf and `e` consists of
   equivalences intertwining every restriction. Transporting its functor laws
   and sheaf condition across these equivalences gives the presheaf with the
   exact displayed carriers and maps. Conversely that presheaf itself supplies
   A and identity equivalences. Thus this realization is equivalent to the
   node, and does not assert only a sheafification result. Exact.
9. Canonical isomorphism natural in F: `p : ...sheafPullback... ≅ A`, with the
   second conjunct specifying A on every sheaf morphism via etale pullback.
   Naturality is therefore in the required section identifications as well as
   in p. The final unit equation fixes the canonical adjunction comparison.
   The quantifiers choose A, e, p once for all F and Y. Exact.
10. Etale normalization: `U : X.Etale`, bijectivity in conjunct three, and
    conjunct four evaluated on every `s : F.obj.obj (op U)`. The helper
    `proEtaleComparisonEtaleSection` applies the etale pullback unit at U and
    then restricts along the diagonal into U times_X U. This is exactly the
    usual identification with the restriction to U_et, in the stated direction.
    The comparison unit in the final equation is the dependency's actual unit.
    Exact.

Edge cases: empty X and empty Y are permitted, with the empty covering governed
by the ordinary sheaf condition. Arbitrary empty-valued sheaves, identity maps,
and non-etale maps g are included. No index type, characteristic, degree n,
ring, nonzero-object, quasi-compactness, separation, or connectedness hypothesis
occurs. Site objects retain universe u+1 and arrows u; set values use the common
larger u+1 universe fixed by the dependencies. No universe equality or extra
smallness instance was introduced; all binders are explicit.

Independent reuse searches (2026-10-15): `msearch.py leanfinder` with
"For a weakly etale scheme over X, sections of the comparison inverse image are
sections of the etale pullback" returned eight hits, on standard-etale pairs
and etaleness of ring/scheme maps, none this sheaf formula. `msearch.py loogle`
with `"ProEt", "sections"` returned zero hits. Independent `rg` searches for
`(proet|pro.et).*(section|pullback|inverse)|comparison.*(section|evaluate)` in
WeilConjectures and project Sheaf, and a focused search in Mathlib's sites,
found no duplicate. Opened `comparisonUpperStarCompUpperStarIso` and
`isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj` in upstream
`Comparison/LowerStarAcyclic`: these concern functor composition and abelian
cohomology, not this set-valued formula. Existing terminal transport was reused
rather than copied. The first worker's LeanSearch service failure is recorded
above; it was not taken as evidence of absence.

H4/H5/H6/H8/H9: both helper definitions contain real constructions, no data
sorry. The sole theorem has whole proof `sorry`; its docstring follows all seven
node proof steps and every declaration has source and blueprint references.
There are no new nodes or dependency modules in this delivery. The newly cited
terminal-transport node is already landed and was checked as described above.
The recorded `lean.statement` was compared verbatim with the theorem signature.
No mathematical or code mismatch was found; no Lean or node changes were needed.
Only this independent reading was appended. Compilation through `scompile.py`
passed for the sole delivered module, including the wrapper's library check;
no errors or additional warnings were emitted.
