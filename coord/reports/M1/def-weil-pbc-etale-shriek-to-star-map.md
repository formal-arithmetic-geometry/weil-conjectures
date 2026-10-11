## Worker report

Existing declaration: `AlgebraicGeometry.Etale.etaleLowerShriekToLowerStar`, in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale`, source lines 651–658.
No module is written: the refreshed upstream already defines the node's map.
The node copy changes only `lean`, recording the declaration's signature verbatim.

Hypotheses and clauses, checked against the source declaration and its section binders:

- Schemes U and X and π : U ⟶ X: upstream `{X Y : Scheme.{u}} (f : X ⟶ Y)`
  with its X = U, Y = X, f = π.
- Finite étale: upstream assumes `[AlgebraicGeometry.Etale f] [IsSeparated f]`.
  Specializing to `[IsFinite π] [Etale π]` supplies separatedness automatically.
  The general separated étale construction covers exactly the requested finite case;
  no condition beyond finiteness and étaleness is required of π.
- A commutative ring Λ and a sheaf of Λ_U-modules M: specialize coefficient category
  `A` to `ModuleCat.{u+1} Λ`, with `Λ : Type (u+1)` and `[CommRing Λ]`, and
  `G : Sheaf U.smallEtaleTopology (ModuleCat.{u+1} Λ)` to M. Category, Abelian and
  Grothendieck abelian structures are the existing module-category instances.
  This uses the authorized constant-coefficient encoding recorded in
  `def-weil-pbc-etale-sheaves`; it does not invent another module category.
- P_M and π_!M: `Etale.etaleLowerShriek A π inferInstance` is the recorded
  definition, namely `sheafToPresheaf ⋙ localization.op.lan ⋙ presheafToSheaf`.
  The Kan extension gives the direct sum indexed by lifts φ, with each summand
  M(V,φ); its unit inserts the summand. `toSheafify` is η_M.
- π_*M: `Etale.lowerStar A π`, written `(π)_*[A]` in upstream's scoped notation,
  evaluates at V as M(V ×_X U), with the recorded base-change restrictions.
- Constant-ring actions: in the authorized ModuleCat encoding the maps are Λ-linear.
  Their extensions to locally constant sections of Λ_X are the canonical actions;
  compatibility is checked locally on a covering where a section of Λ_X is constant.
  Pullback preserves constant scalars, hence gives the stated gamma and theta actions.
  The SheafOfModules encoding and its comparison are the existing project's separate
  encoding (a bridge belongs to stage 3, as the dependency's record explicitly says).
- The graph extension c^p: upstream `Scheme.Etale.graphExtend` (lines 295–298)
  is constructed by the unique complementary-open gluing of `(identity, zero)`.
  `graphExtend_graph` and `graphExtend_graphComplι` give respectively the input on
  the graph and zero on the complement; `graph_hom_ext` gives uniqueness.
  These are exactly the summand maps in the node, not an arbitrary linear map.
- The canonical c_M: the definition takes the inverse adjunction hom equivalence
  of `Etale.lowerStarUnit A π |>.app M`. Its components are precisely graphExtend.
  `etaleLowerShriekRestrictionAdjunction` is the adjunction for the same left
  Kan extension followed by sheafification. Under the Kan adjunction the graph
  family is c^p; under the sheafification adjunction its mate is the unique map
  c with `toSheafify ≫ c.hom = c^p`. Thus the construction is exactly the required
  universal-property factorization, even though upstream expresses both adjunctions
  together rather than naming c^p as a separate definition.
- Naturality: `lowerStarUnit` is a natural transformation in M, with naturality
  proved using `Scheme.Etale.graphExtend_natural`. Naturality of the inverse
  adjunction hom equivalence gives
  `etaleLowerShriek.map α ≫ c_M' = c_M ≫ lowerStar.map α`, exactly the node's
  equation with Lean's order of composition. No naturality hypothesis is added.

Dependency declarations read and used to identify the existing construction:

- `Mathlib.CategoryTheory.MorphismProperty.Comma`: `MorphismProperty.Over`;
  `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`: `Over.pullback`.
  The finite étale category is the indicated specialization; the map itself uses
  individual finite étale morphisms, so no replacement category is needed.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `Sheaf.AlgebraicGeometry.EtaleSheaves`: the record authorizing the ModuleCat
  encoding (the set-valued predicates are not needed by this definition).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`, the general-site
  notion named by `def-weil-sheaf-of-modules-category`'s mathlib_match.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `Etale.etaleLowerShriek`, `Etale.etaleLowerShriekUpperStarAdjunction`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationAdjunction`; the corresponding
  ModuleCat-valued sheafification adjunction is `CategoryTheory.sheafificationAdjunction`
  in `Mathlib.CategoryTheory.Sites.Sheafification`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`.
- `Sheaf.AlgebraicGeometry.EtaleGraphSectionExtensionMap`:
  `etale_graph_section_extension_map`, characterizing exactly the same extensions.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `etaleInverseImageModulesExact`, giving the ring map and module interpretation.
- `Sheaf.AlgebraicGeometry.EtaleGraphSectionExtensionMapLinear`:
  `etale_graph_section_extension_map_linear` was read. Its current Lean record only
  asserts existence of a Λ-linear natural transformation, without the graph condition
  or full Λ_X action described in its prose. It is not needed to choose the map here:
  the upstream graphExtend construction supplies the exact map and linearity, rather
  than choosing the unspecified existential witness. No dependency repair is necessary
  to record this existing exact construction.
- `def-weil-pbc-scheme-conventions` is a convention record, not a declaration.

Edge cases: empty U (empty sums, zero sheaf and unique zero comparison), empty X,
zero M and the zero coefficient ring all remain covered. The identity morphism's
only graph is the whole scheme, so the construction identifies with the identity.
For a disjoint union of two copies the two graph summands map into the corresponding
components, so this is not a zero or arbitrary comparison. No characteristic or
nonemptiness hypothesis appears. Universes match the existing small-site convention;
smaller coefficient rings can be lifted as in the project's established encoding.

Searches made:

1. `msearch.py leanfinder`, query "canonical natural map from etale extension by zero
   to direct image of module sheaves": eight unrelated algebraic étale/differentials
   hits; no Mathlib match.
2. `msearch.py loogle`, query "presheafToSheaf, sheafificationAdjunction": no hits;
   the service reports unknown identifier presheafToSheaf. Local Mathlib source
   confirms the sheafification adjunction and its universal property.
3. `msearch.py grep`, regexp
   `etaleLowerShriekToLowerStar|shriekToStar|etaleShriekToStar`: no Mathlib hits.
   `rg` of that regexp and the node id in WeilConjectures and lean/Sheaf finds
   the exact upstream declaration in UpperLowerStar/FiniteEtale.lean, line 654,
   and its comparison/isomorphism results; no matching Sheaf declaration.
   The upstream-name JSON search has no hit, so that older index is not definitive.
   The source declaration, its full section context, docstring, graph construction,
   and its adjunction were read directly.

Source checked: https://stacks.math.columbia.edu/tag/0F4L, proof's first paragraph
and graph construction. The local literature checkout on this machine contains
citation lists but not etale-cohomology.tex; the official tag supplies the source.
No statement correction, new node, proof or module is needed. The old node's searches
predate this upstream addition. The final delivery dry run is the validation for
this existing-declaration record; no new Lean file requires compilation.

## Second reading by M1

Independent reading of the node copy, every statement-dependency record, and the
upstream definition and its section binders. Verdict: the recorded existing
construction is the requested canonical map, specialized to finite etale morphisms
and module coefficients. Keep the definition record and its verbatim signature;
write no duplicate module. No statement correction, new node, or dependency module
is part of this delivery.

Source: read the actual Stacks `etale-cohomology.tex` from its official source,
lines 11516–11575, labels `lemma-shriek-into-star-separated-etale` (0F4L) and
`lemma-shriek-equals-star-finite-etale` (03S7), as well as
https://stacks.math.columbia.edu/tag/0F4L. The local literature copy lacks this tex
file. The source assumes separated etale, arbitrary schemes and abelian/module
sheaves; there is no standing Noetherian, field, characteristic or nonemptiness
assumption. This definition node isolates the construction; injectivity and the
finite-etale isomorphism are separate nodes, not additional clauses here.

Objects, hypotheses and conclusion, matched individually:

1. Schemes U, X and pi: upstream `{X Y : Scheme.{u}} (f : X ⟶ Y)`, with X = U,
   Y = X and f = pi. PASS.
2. Finite etale pi: specialize `[AlgebraicGeometry.Etale f] [IsSeparated f]` to
   `[Etale pi] [IsFinite pi]`. Finite implies separated by the existing instance,
   checked by compilation. Upstream defines the source's more general map;
   its finite restriction is exactly the node's map. No extra hypothesis. PASS.
3. Commutative ring Lambda and M in modules over the constant ring sheaf on U:
   specialize `(A : Type u') [Category.{u+1} A] [Abelian A]
   [IsGrothendieckAbelian.{u+1} A]` to `ModuleCat.{u+1} Lambda`, with
   `Lambda : Type (u+1)` and `[CommRing Lambda]`, and G to
   `M : Sheaf U.smallEtaleTopology (ModuleCat.{u+1} Lambda)`.
   The coefficient instances synthesize. Read the `def-weil-pbc-etale-sheaves`
   record's explicit decision of L authorizing this encoding for six functors.
   It coexists with `SheafOfModules` over the constant ring sheaf; its equivalence
   is deferred to stage 3. This delivery uses the authorized encoding. PASS.
4. P_M, its graph-indexed summands and restriction maps: read
   `Etale.etaleLowerShriek` in `LowerShriek/EtaleMap.lean`, and Mathlib
   `Functor.sheafPullbackConstruction.sheafPullback` in `Sites/Pullback.lean:70`.
   The presheaf is `sheafToPresheaf ⋙ localization.op.lan`, with localization
   `MorphismProperty.Over.map ⊤ h`. Its Kan unit inserts the section on the
   object over U corresponding to each lift. Thus it is the same sum presheaf,
   not an unrelated presheaf or an arbitrary map. PASS.
5. pi_!M = P_M sheafified and eta_M: the final factor is `presheafToSheaf`;
   eta is `toSheafify` on this Kan extension. Read both the ModuleCat-valued
   sheafification adjunction and `PresheafOfModules.sheafification` with its
   hom equivalence in Mathlib. The former is the authorized encoding of the
   latter for these constant coefficients. PASS.
6. pi_*M and its restrictions: `Etale.lowerStar` in `UpperLowerStar/Defs.lean:162`
   is the sheaf pushforward along `Over.pullback @Etale ⊤ pi`, hence evaluates
   to M on V times_X U. The `lowerStar_obj_val_obj` signature confirms this.
   Read `Over.pullback` itself; its objects and arrows are actual scheme fibre
   products and their induced maps. PASS.
7. Constant-ring actions theta and gamma: in the ModuleCat encoding scalar
   linearity is in the morphism types. To recover the stated constant-sheaf
   action, work locally where a section of the constant ring sheaf comes from
   Lambda. Restriction along the graph and along the base-change projection
   preserves those scalars; this gives respectively theta and gamma. Equality
   and linearity glue by the sheaf condition. Read the constantSheaf definition
   and `etaleInverseImageModulesExact`'s gamma/constant-section conditions. PASS
   within the project's explicitly authorized encoding; no new bridge asserted.
8. c^p_M is precisely extension on graphs and zero off them: in
   `FiniteEtale.lean:295`, `Scheme.Etale.graphExtend` chooses the unique glued
   `(identity, zero)` morphism for the complementary graph opens.
   `graphExtend_graph` and `graphExtend_graphComplι` give its two restrictions;
   `graph_hom_ext` gives uniqueness. `lowerStarUnit` at line 348 has exactly
   these components, with naturality both in the site object and in M. Under
   the Kan hom equivalence this is the sum of these extensions. PASS.
9. c_M and unique factorization c_M composed with eta_M = c^p_M: the definition
   at lines 654–658 is the inverse hom equivalence of
   `etaleLowerShriekRestrictionAdjunction` applied to `lowerStarUnit.app M`.
   Read that adjunction, `etaleLowerShriekUpperStarAdjunction`, and Mathlib
   `sheafAdjunctionContinuous` at `Sites/Pullback.lean:75`: the last is the
   composite of the Kan adjunction and sheafification adjunction, restricted
   along the fully faithful sheaf inclusion. The two right-adjoint transports
   cancel (the localization-restriction isomorphism and its inverse).
   Thus its mate is exactly the unique sheafification factorization, not merely
   a map with the same source and target. PASS.
10. Naturality for every module morphism alpha: `lowerStarUnit.naturality`,
    supplied by `Scheme.Etale.graphExtend_natural`, together with
    `Adjunction.homEquiv_naturality_left_symm` and right naturality gives
    `etaleLowerShriek.map alpha ≫ c_M' = c_M ≫ lowerStar.map alpha`.
    This is the node's equation in Lean's composition order. PASS.

Dependency check: also opened the signatures of `MorphismProperty.Over`,
`Over.pullback`, `Scheme.smallEtaleTopology`, `SheafOfModules`, `constantSheaf`,
`PresheafOfModules.sheafification`, the graph-extension module and the inverse-image
module. The finite-etale category record is the indicated infimum specialization
of Over; the scheme-conventions record adds no notion. The recorded
`Scheme.Modules` in the general modules-category node is not used as a category
of etale modules: its Mathlib match is `SheafOfModules`, and the etale-sheaves
record authorizes the ModuleCat encoding used here.

Mismatch already noted by the worker, independently confirmed: the separate
`etale_graph_section_extension_map_linear` signature asserts only existence of a
Lambda-linear natural transformation, with neither graph characterization nor the
full constant-ring action. Its docstring describes more than that signature.
It is not used to select this map. The exact upstream graph construction supplies
the map instead, so no dependency module is needed to type or identify this
existing construction. The node's prose and dependency list remain unchanged.

Edge cases: no lifts gives an empty sum (zero); an empty source gives the zero
comparison; an empty base forces the source empty and the construction still
exists. Zero M and the zero commutative ring are allowed. The identity has graph
the whole object and gives identity under the canonical identifications. Two
copies give inclusion into the corresponding components, ruling out an arbitrary
zero map. No n occurs, no positive-characteristic restriction, and no finite or
nonempty index assumption appears. `u` is arbitrary, and the coefficient object
universe `u'` is independent; the ModuleCat specialization uses the established
site universe u+1. Universes can be raised to include smaller coefficients and
schemes; no case requires a field or finite ring.

Independent searches (queries differ from the worker's):

- `msearch.py leanfinder`: "sheafification of graph extension gives a natural
  transformation from etale shriek to pushforward". Eight generic sheafification
  and site hits, no scheme-level comparison.
- `msearch.py loogle`: `CategoryTheory.Adjunction.homEquiv_naturality_left_symm`.
  Found the exact adjunction naturality lemma used to check clause 10.
- `msearch.py grep`: `graphExtend|lowerStarUnit|extension by zero off`.
  No Mathlib hits. Independent rg in WeilConjectures and lean/Sheaf finds
  `FiniteEtale.lean`'s exact construction, and the separate open-immersion and
  compactification comparisons, which are different constructions with different
  domains. No new definition is justified.

Validation: sandbox-only `scratchpad/Check.lean` imports the upstream module and
checks the finite-etale ModuleCat specialization, separatedness and coefficient
instances under the project's strict auto-implicit settings. It contains no new
library declaration and is excluded from delivery. No Lean module is changed or
proved in this delivery. Existing upstream docstrings and proofs are read-only;
H8/H6 do not require rewriting them. Second reading changes only this report,
adding the independent clause checks, searches and validation.

Validation result: the scratch check compiled cleanly in 1.9 seconds.
`#print axioms Etale.etaleLowerShriekToLowerStar` lists only `propext`,
`Classical.choice`, and `Quot.sound`. The delivery dry run passed preflight;
there are no new library modules to compile on the server.
