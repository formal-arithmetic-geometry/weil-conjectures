## Worker report

Item: lem-pur-site-algebraic-composition-unit. Group O2, stage 2, 2026-10-21.

The delivery states `CategoryTheory.siteAlgebraicCompositionUnit` in
`Sheaf.CategoryTheory.SiteAlgebraicCompositionUnit`. Its proof is `sorry`.
The five helper definitions contain real data or explicit propositions; none
postpones data or adds a theorem without a DAG statement. They belong to the
owning node's comparison and are listed in `lean.declarations`.
No statement correction, dependency repair, or new definition node is needed.

Hypothesis-by-hypothesis reading:

- The three small sites are categories `C`, `D`, `E` with Grothendieck topologies
  `J`, `K`, `L`. The site object and morphism universes `uC,vC,uD,vD,uE,vE`
  remain independent. The sheaf universe is `max uC vC uD vD uE vE w`.
  Thus every site is small in that fixed larger universe, and `w` permits
  arbitrary further enlargement. This implements def-weil-size-convention.
  Using their generated Grothendieck topologies is the existing representation
  of sheaves in def-weil-pbc-sites-and-cohomology; no subcanonicity or existence
  of arbitrary pullbacks of site objects is imposed.
- The functors are the explicit binders `(v : C ⥤ D)` and `(u : D ⥤ E)`.
- Precomposition preserving set sheaves is exactly `[v.IsContinuous J K]`
  and `[u.IsContinuous K L]`, with Mathlib's sheaf-preservation definition of
  continuity, not an extra covering-preservation assumption.
- `sheafPullback v ... J K` and `sheafPullback u ... K L` are explicitly from
  `Functor.sheafPullbackConstruction`. They are `sheafToPresheaf ⋙ op.lan ⋙
  presheafToSheaf`, the specified comma colimit followed by sheafification.
  `siteAlgebraicCompositePullback` uses that same construction for `v ⋙ u`,
  installing Mathlib's proved composite continuity locally in its definition.
  The identity uses that construction for `𝟭 C`.
- `siteAlgebraicCompositeAdjunction` is the recorded constructed adjunction
  for `v ⋙ u`, with its definitionally equal right adjoint written as
  `u.sheafPushforwardContinuous ... ⋙ v.sheafPushforwardContinuous ...`.
  The individual and identity units are those of the recorded constructed
  `sheafAdjunctionContinuous`; none is freely chosen.
- The three `[PreservesFiniteLimits ...]` binders are precisely the three
  finite-limit hypotheses on `L_v`, `L_u`, `L_uv`. No such binder is imposed
  on `L_id`.
- The algebraic lifts in the statement are quantified as the dependency's
  `SheafOfModules.AlgebraicInverseImageOfUniverses`. These are exactly the
  prescribed transported ring and module operations and their underlying
  identifications. The same fixed larger universe is used for rings, modules
  and set sheaves; `uliftFunctor.{s,s}` retains the dependency's representation
  without changing that universe. The explicit `HasSheafCompose` binders in
  the generic predicates are the typing requirements of that recorded
  presentation. At the main theorem's larger universe they are inferred,
  without any new mathematical hypothesis on the sites or lifts.

Clause-by-clause reading of the conclusion, in conjunction order:

1. `siteAlgebraicCompositionIso` is an actual natural isomorphism from the
   constructed composite to the iterated constructed inverse image. Its
   definition is `leftAdjointUniq` applied to the specified composite-site
   adjunction and the `Adjunction.comp` of the two individual adjunctions.
   The first conjunct states `eta_uv ≫ P_v(P_u(gamma_H)) =
   eta_v ≫ P_v(eta_u)`, the node's displayed unit equation in Lean's
   left-to-right composition convention.
2. The second conjunct evaluates that equation at every input sheaf `H`,
   object `W : C`, and section `x : H(W)`. Its left side applies gamma at
   `u(v(W))` to the composite unit section; its right side applies the
   v-unit and then the u-unit. These are exactly the inverse-image sections
   in the node, without an assumption that arbitrary output sections have
   single colimit representatives.
3. The third conjunct quantifies over every competing natural isomorphism
   `δ` and imposes only the section equation as its premise, concluding
   `δ = siteAlgebraicCompositionIso ...`. Combined with the preceding
   equations, this is existence and uniqueness with either normalization.
4. The fourth conjunct is `gamma_(A×B) ≫ p1 = p0 ≫
   prod.map gamma_A gamma_B`. Here `prodComparison` is Mathlib's canonical
   map whose projections are the functor images of the product projections.
   Finite-limit preservation makes both comparisons isomorphisms; it also
   makes the composite `L_v ⋙ L_u` preserve products. The source's `p1` is
   therefore also the successive product comparison.
5. The fifth conjunct is `gamma_* ≫ terminalComparison L1 =
   terminalComparison L0`, the node's terminal equation, again using the
   canonical comparisons rather than unspecified product structures.
6. `SiteAlgebraicComparison gamma.hom` expands the ring/module claims for
   every ring sheaf `R` and every pair of transported presentations `A₀,A₁`.
   It supplies a ring-sheaf isomorphism `eR : R₀ ≅ R₁`. Its image under the
   lifted forgetful functor is required to equal
   `A₀.ringUnderlying.inv ≫ gamma_R ≫ A₁.ringUnderlying.hom`.
   Consequently it is exactly gamma under the dependency's identifications,
   not merely some ring isomorphism between the output rings. Ring morphisms
   preserve zero, one, addition and multiplication by their type.
   The supplied `eM` is a natural isomorphism of AddCommGrp-valued sheaf
   functors on the original module category. Its underlying set map is
   required to equal `A₀.moduleUnderlying.hom ≫ gamma_M ≫
   A₁.moduleUnderlying.inv`. Thus it is additive, preserves zero, is
   invertible, and is natural on every module morphism. The final quantified
   equality is `eM(a • x) = eR(a) • eM(x)` for every module, every site
   object `V : Eᵒᵖ`, every coefficient `a`, and every local section `x`.
   The module morphism categories are `ringedSiteModules`, the dependency's
   transparent abbreviation of Mathlib `SheafOfModules`. For an iterated
   lift its operations are the operations of `L_v ⋙ L_u`, as the product
   calculation in proof step 5 explains.
7. The seventh conjunct asserts `IsIso` for the specified identity-adjunction
   unit at every set sheaf. Its type reduces `P_id` to the identity functor,
   so its source is the original sheaf and target is `L_id H`.
8. `SiteAlgebraicIdentityUnit` quantifies over every transported presentation
   of `L_id`. It supplies `eR : R ≅ RI` whose underlying map is precisely
   `eta_R ≫ A.ringUnderlying.hom`, and a natural additive isomorphism from
   the original module functor to the transported module functor, whose
   underlying map is `eta_M ≫ A.moduleUnderlying.inv`. Its final equation
   is semilinearity on every local section through that same `eR`.

The predicates in clauses 6 and 8 merely group the owning theorem's long
algebraic clauses. They define no replacement algebraic inverse image,
ring sheaf, module category, or functor on algebraic objects.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: the recorded site convention;
  sheaf categories are its existing Grothendieck-topology representation.
- def-weil-size-convention is metatheoretic and has no declaration or module;
  its explicit-universe requirement is implemented as described above.
- `Mathlib.CategoryTheory.Sites.Pullback`,
  `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` and
  `.sheafAdjunctionContinuous`: the recorded Mathlib match and specified unit.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`,
  `SheafOfModules.AlgebraicInverseImageOfUniverses`: full recorded interface,
  including all generalized-section graph equations and module naturality.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`: the recorded general module category.
- Proof dependencies are supplied by `Mathlib.CategoryTheory.Adjunction.Basic`
  (transitively through Pullback; `Adjunction.comp` and `Adjunction.id`),
  `Mathlib.CategoryTheory.Adjunction.Mates` (`unit_conjugateEquiv_symm`),
  and `Mathlib.CategoryTheory.Adjunction.Unique` (`leftAdjointUniq` and its
  unit equation). No additional DAG hypothesis or proof ingredient is invented.

Sources read: sites.tex labels lemma-composition-morphisms-sites (03CB),
lemma-adjoints-u (00VE), lemma-adjoint-sheaves (00WX),
proposition-sheafification-adjoint (00WH), and the operation transport of
sites-modules.tex lemma-pullback-module (03D2). The blueprint ancestor's
finite-Kummer-level proof was read in main-20261015; its final sentence is
naturality of the tensor projection under base change. This lemma supplies
only the set/ring/module comparison needed there, not a tensor assertion.
The theorem docstring gives all eight node proof steps and the dependency IDs.

Edge cases checked before and after writing:

- Empty site categories are permitted; all section quantifiers are then
  vacuous while the natural-isomorphism and adjunction assertions remain.
- Singleton/trivial sites and identity functors are permitted. No distinctness
  of sites or functors, nonempty category, or nonidentity-unit assumption occurs.
- Zero ring and zero module are permitted. No nontriviality or invertibility
  of scalars is assumed; the scalar equation remains the usual zero equation.
- Arbitrarily large coefficient sheaves in the fixed universe and different
  site object/morphism universes remain allowed. No universe equality was added.
- Terminal sheaves are included in the comparison and in the constant-operation
  transport. No site terminal object or representable terminal sheaf is assumed.
- The identity lift has no extra finite-limit assumption. Its unit is the
  actual adjunction unit, not an arbitrary identification or a chosen map.

Searches (msearch.py O2, logged in sandbox searches.jsonl):

- LeanFinder: "Unit normalized composition isomorphism for sheaf inverse images
  respects ring and module operations and the identity unit". Eight hits,
  principally free-module pullback compatibility and unit formulas; no full match.
- Loogle: `SheafOfModules.pullbackComp`. Five hits including pullbackComp,
  pullback_comp_id, pullback_id_comp, pullback_assoc and its conjugate equation.
  Source signatures read: these are module pullbacks with specified ring maps,
  not this specified set-sheaf compositor and all algebraic/section clauses.
- Mathlib grep: `sheafPullbackComp|sheafPullbackId|prodComparison_naturality`
  in CategoryTheory. No hits. The canonical product and terminal comparisons
  were then read in Limits/Preserves/Shapes/BinaryProducts and Terminal.
- LeanSearch: "Unit normalized composition of sheaf inverse image respects ring
  and module operations". Eight hits, again module pullbackComp and unrelated
  unit/additive statements; no full match.
- `rg` in live WeilConjectures and Sheaf for the item ID and chosen declaration
  names found no duplicate. Broader composition/module searches found the
  site-generator compositor and etale/module-specific linearity interfaces.
  Their sources were opened: neither states the present algebraic result for
  arbitrary sites, all ring sheaves and their algebraic presentations.
- `dag/lean_names_upstream.json` contains none of the six new declaration names.

Validation: only the prescribed scompile.py wrapper was used. The preliminary
unscoped diagnostic options were removed; the final module has no diagnostic
commands, extra proofs, private/local definitions or instances, or unbound
variables. One named theorem has the expected `sorry` proof.

## Second reading by O2

I reopened the node and final file in a separate reading pass. This is a second
pass by the same dispatcher-started worker; no second agent was started, in
accordance with the explicit brief. The maintainer performs independent review.

I checked the three finite-limit binders and the absence of one for L_id,
the constructed adjunction rather than a chosen left adjoint, the compositor's
direction, both nested unit applications and their site evaluation points,
section-only uniqueness, and the orientation of both comparison equations.
I unfolded both algebraic predicates and checked the source/target of every
ring and module identification. The output ring isomorphism, natural additive
isomorphism and their sectionwise scalar equation all use the same maps.
For identity the source ring and modules are the originals, and the underlying
maps are the actual unit components. Universes on every call of the three
site helpers were made explicit so independent conjuncts cannot introduce
unrelated universe parameters. During compilation the target section types
in scalar equations required explicit `@id` casts to the existing module
carriers; these change no mathematical structure. The only remaining sorry
is the node's main theorem. No mismatch with the unchanged node was found.
