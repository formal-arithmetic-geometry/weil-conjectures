## Worker report

Item: lem-a1-clopen-relation-base-change-identification. The module
`Sheaf.AlgebraicGeometry.ClopenRelationBaseChangeIdentification` states
`AlgebraicGeometry.clopen_relation_base_change_identification`, with its sole proof
postponed by `sorry`. There are no definitions, extra nodes, dependency repairs,
or statement corrections. The node copy changes only `lean`.

Source checked directly: literature/stacks-project/groupoids.tex, the definition of
an equivalence relation, lemma-restrict-relation, definition-restrict-relation, and
Tag 02VD (lemma-restrict-groupoid-relation), including its displayed Cartesian formula;
literature/stacks-project/more-groupoids.tex, Tag 03X5, conclusion (h) and its clopen
inverse-image argument. The node is an auxiliary node, not the blueprint unit's own
statement. Its source and six-step proof are rendered in the declaration docstring.

Hypotheses and clauses, in the order of the node:

- Schemes T,U,R and arbitrary B: `{T U R B : Scheme.{u}}`. Structure maps are `fU`,
  `fR`; `s t` are scheme morphisms, and `hs ht` assert they are over T.
- Identifying R(H) with an equivalence relation: `hrel` quantifies over every scheme
  H and fixed `hH : H ⟶ T`. Its first conjunct is injectivity of the endpoint-pair
  map on `{g : H ⟶ R // g ≫ fR = hH}`. Its second is `Equivalence` of the relation
  defined by existence of an R-valued point with the specified endpoints on
  `{g : H ⟶ U // g ≫ fU = hH}`. The witness is automatically over T by `hs`.
  In particular this retains monicity, not only the weaker pre-equivalence property.
- Arbitrary base change: `(fB : B ⟶ T)`; `pullback fU fB` and `pullback fR fB`
  are exactly U_B and R_B. The four equalities defining the existential `sB tB`
  specify their U- and B-projections, hence determine the canonical induced maps.
- Induced clopen subscheme V: `V : (pullback fU fB).Opens`, with `hV : IsClopen
  V.carrier`; `V.toScheme` is the actual restricted locally ringed space.
- C is the induced open intersection: `C = (sB ⁻¹ᵁ V) ⊓ (tB ⁻¹ᵁ V)`, with
  `IsClopen C.carrier`. D is its induced open complement by `IsCompl C D` in the
  lattice of opens. Thus C and D use restricted structure sheaves, with no abstract
  scheme replacing either restriction.
- R_B = C ⨿ D: `Nonempty (IsColimit (BinaryCofan.mk C.ι D.ι))`. This is the
  coproduct universal property with vertex R_B and the actual two inclusions.
- The two maps to V: existential `sC tC` satisfy `sC ≫ V.ι = C.ι ≫ sB` and
  the corresponding target equality. The open immersion makes these unique.
- First canonical isomorphism: `e : C.toScheme ≅ pullback (pullback.snd V.ι sB ≫
  tB) V.ι`, the exact iterated fibre product. The next three equalities preserve
  the middle R_B projection and both V projections, specifying the isomorphism.
- Original relation map: `j : R ⟶ pullback fU fU` has projections s,t. The map
  `m` from `pullback (V.ι ≫ pullback.snd fU fB) (V.ι ≫ pullback.snd fU fB)`
  to U ×_T U has both prescribed V-to-U projections. Thus `pullback m j` is
  exactly (V ×_B V) ×_(U ×_T U) R, with the B-product, as required.
- Its canonical map to R_B: `k` has R-projection `pullback.snd m j` and the
  common B-coordinate from the first V-coordinate. These two equations determine k.
- Second canonical isomorphism: `e'` goes from the iterated pullback to `pullback
  m j`. Its three equations preserve k and both V projections. Together with e
  this gives the entire displayed chain, compatible with every required map.
- H-points over every B-scheme: the final `∀ (H : Scheme.{u}) (hH : H ⟶ B)`
  first gives the unique lift of every U(H)-point over `hH ≫ fB` to U_B(H),
  with its two projections fixed. This spells out the stated relative identification.
- V(H) is a subset of U_B(H): `Function.Injective` of postcomposition with `V.ι`
  on the subtype of B-valued points. With the preceding unique lift this is also
  its identification with the specified subset of U(H).
- C(H) consists exactly of the R(H)-points with both endpoints in that subset:
  for every r over T the `↔` says its unique lift through C exists precisely when
  both r s and r t factor through V over the fixed hH. Both endpoint factorizations
  explicitly retain their B-coordinate.
- The final two conjuncts assert injectivity of the C endpoint-pair map on
  B-valued points and `Equivalence` of the relation on V(H) defined by sC,tC.
  The witness c is automatically over B using the source compatibility above.

Dependency declarations read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- def-pc-fibre-product: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, its fst/snd projections, lift/map universal
  properties. Scheme pullbacks are supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`. Its concrete induced-open interface is
  `Scheme.Opens.toScheme`, `Scheme.Opens.ι` in `Mathlib.AlgebraicGeometry.Restrict`.
- Proof leaf lem-weil-pbc-scheme-coproduct-family: Mathlib.AlgebraicGeometry.Limits,
  the discrete-colimit instance, `AlgebraicGeometry.sigmaOpenCover`, and
  `AlgebraicGeometry.disjoint_opensRange_sigmaι`; binary coproducts are the finite case.
- Proof leaf lem-weil-pbc-scheme-morphism-gluing: Mathlib.AlgebraicGeometry.Gluing,
  `AlgebraicGeometry.Scheme.Cover.glueMorphisms`, `ι_glueMorphisms`, `hom_ext`.
- Proof leaves lem-weil-pbc-morphism-factors-through-open-subscheme and
  lem-weil-pbc-open-immersion-monomorphism: Mathlib.AlgebraicGeometry.OpenImmersion,
  `AlgebraicGeometry.IsOpenImmersion.lift`, `lift_fac`, `lift_uniq`, `mono`.
  All proof dependency modules are imported; Gluing is a plain proof import.

Edge cases checked mathematically: V empty gives empty C and D=R_B; V=U_B gives
C=R_B and empty D. Empty B and empty H are included, without nonemptiness binders.
Disconnected H causes no pointwise/underlying-topological-point confusion: all
points here are scheme morphisms, with the same fixed B-coordinate throughout.
The diagonal relation restricts to the diagonal of V. The total relation restricts
to V ×_B V, not the T-product. No invariance, groupoid multiplication, separation,
etaleness, affineness, or finiteness assumption is introduced. The single universe
u is explicitly bound for the category of schemes and its test schemes; `autoImplicit
false` verifies no variable is silently introduced. All maps named existentially
are fixed by projection equations, rather than arbitrary maps supplied as hypotheses.

Searches (2026-10-24):

- msearch.py leanfinder: “Base change of a scheme equivalence relation restricted
  to a clopen open subscheme is an iterated fibre product”. Eight hits, including
  Scheme.Pullback.diagonalRestrictIsoDiagonal, openCoverOfBase_f, and carrierEquiv;
  none contains the complete clopen decomposition, both identifications, and
  pointwise equivalence assertion.
- msearch.py loogle: `"pullback", "IsOpenImmersion"`. Twelve hits on locally ringed
  space pullbacks of open immersions; ingredients only.
- msearch.py grep: `restrict.*[Rr]elation|[Rr]elation.*restrict|[Ii]sClopen.*pullback`
  in AlgebraicGeometry. No hits.
- Direct rg of the same concepts, clopenRelation/restrictedRelation/relationBaseChange,
  and the proposed declaration name in Mathlib, lean/WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json. Direct grep of the node id in WeilConjectures: no match.
  Related project statements ProperEtaleRelationFiniteNeighbourhood and
  EtalePullbackRelationPresheaf add etaleness/quotient hypotheses or conclusions and
  do not state this node. The existing restrictedEtaleRelation helpers are Over-S
  versions of the iterated product, not these scheme pullbacks; no competing
  definition was introduced. All three wrapper searches are in searches.jsonl.

Validation: scompile.py checked the module in sandbox and named-library mode, cleanly,
with no warning, at the default 60-second limit. Initial elaboration exposed ambiguous
coercions from scheme opens to sets; using the existing `.carrier` field fixed that.
The theorem proof remains exactly `by sorry`. No STATEMENT-DISPUTED issue found.

## Second reading by Q48

The dispatched worker reread the node and the final module clause by clause as
listed above, checking projection order and the fixed B-coordinate in the last
clauses. This is a worker self-check; no independent worker review is claimed.
The brief prohibits starting other agents; the maintainer's independent delivery
review remains the independent reading. No mathematical mismatch or node correction
was found. The only compiler repair was to spell the carrier of an open explicitly.
