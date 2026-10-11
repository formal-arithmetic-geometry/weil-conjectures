## Worker report

The module states functoriality of the étale Mayer–Vietoris long exact sequence for a two-open cover under a scheme morphism. It introduces restriction maps `rU`, `rV`, `rI`, connecting maps `δX`, `δY`, exactness clauses, and the connecting-square compatibility under `Etale.cohomologyMap`. The cover hypothesis is `hcover : U ⊔ V = ⊤`; `g` is a morphism `Y ⟶ X`; `G` is an abelian étale sheaf on `X`.

The first exactness clause renders injectivity in degree zero and exactness of the middle pair-to-intersection map and the connecting map. The final clause renders commutation of the connecting maps with pullback along the restricted morphism `g ∣_ (U ⊓ V)` and global pullback `g`. The pullback maps are Mathlib/source declarations `AlgebraicGeometry.Etale.cohomologyMap`.

Dependencies used: `def-pc-scheme` (Mathlib `AlgebraicGeometry.Scheme`), `def-weil-pbc-abelian-etale-sheaves` (`CategoryTheory.Sheaf`), `def-weil-pbc-cohomology-pullback` (`AlgebraicGeometry.Etale.cohomologyMap`), `lem-weil-pbc-inverse-image-composition` (`AlgebraicGeometry.Etale.lowerStarComp`), and `lem-weil-pbc-etale-mayer-vietoris` (`AlgebraicGeometry.Etale.etale_mayerVietoris`).

Edge cases checked: the cover is allowed to have empty opens; `q = 0` is explicit for injectivity; the intersection is `U ⊓ V`; no nonemptiness, separation, or finiteness hypotheses are added.

Searches: `msearch.py leanfinder` and `loogle` for Mayer–Vietoris naturality returned only one-site Mayer–Vietoris declarations; grep of Mathlib and `WeilConjectures` found no declaration expressing pullback naturality. Existing declarations were checked with `#check` in a scratch module.

## Earlier second reading (a previous round; superseded)

I reread the node and module. The hypotheses `g`, `U`, `V`, `hcover`, and `G` are all explicit. The module introduces the three restriction maps and both connecting maps, states degree-zero injectivity and exactness, and states the connecting square after pullback. The edge cases (empty opens and degree zero) remain included. No mismatch was found in the rendered Lean clauses.

## Second reading by V1

I opened the item node, all five statement-dependency nodes and their recorded declarations,
the delivered module, and Stacks `etale-cohomology.tex`, section Étale cohomology,
`lemma-mayer-vietoris` (Tag 0A50), including its proof. The Stacks checkout available on
this machine supplies the same source text under `c1-stacks-review`. The section assumes
only a scheme, two covering opens, and an abelian étale sheaf. As the node explicitly
records, pullback compatibility itself is an agent-identified consequence, not a theorem
stated verbatim in Stacks. Its five-step proof agrees with the source's construction.
There is no node statement correction, no new node, and no dependency module.

Object/hypothesis/conclusion inventory and Lean match:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Schemes X and Y and arbitrary morphism g : Y → X | `{X Y : Scheme.{u}} (g : Y ⟶ X)` | Same Mathlib scheme and scheme morphism as def-pc-scheme; no property instance on g. |
| Two opens U,V covering X | `(U V : X.Opens) (hcover : U ⊔ V = ⊤)` | Exactly two arbitrary open subschemes and their union condition. |
| U′,V′ and their intersection on Y | `g ⁻¹ᵁ U`, `g ⁻¹ᵁ V`, `g ⁻¹ᵁ (U ⊓ V)` | Inverse-image opens. Preimage preserves union, intersection, and top, so they cover Y and the last is their intersection. These are derived facts, not extra hypotheses or conclusions. |
| Restricted morphisms g_W for W=U,V,U∩V | `g ∣_ U`, `g ∣_ V`, `g ∣_ (U ⊓ V)` | Mathlib morphism restriction, with `morphismRestrict_ι` verifying the named square. |
| Abelian sheaf G on X_ét | `G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` | The exact recorded specialization of def-weil-pbc-abelian-etale-sheaves. |
| Inverse image g⁻¹G and open restrictions | `(upperStar AddCommGrpCat.{u + 1} g).obj G` and the analogous open-immersion objects | The existing upstream inverse-image functor, not a private copy; open restrictions are inverse images. |
| H^q of the listed sheaves, q≥0 | `Sheaf.H ... q`, `q : ℕ` | The encoding used by def-weil-pbc-cohomology-pullback: Ext of the constant integer sheaf. Its resolution interpretation is the recorded stage-3 bridge, not a new cohomology definition. |
| Global vertical pullback g* | `cohomologyMap g G q` | Opened TopologicalInvariance: the recorded exact-functor Ext map with the constant-sheaf comparison. No universal-homeomorphism assumption occurs in this definition's section. |
| Vertical maps on each open, with the stipulated coefficient identification | `pU`, `pV`, `pI`, each fixed by a `∀ q, p... q = ...` conjunct | Exactly `cohomologyMap (g ∣_ W)` followed by `Sheaf.H.map` of the two composition comparisons. The first `upperStarComp` inverse maps nested pullback to pullback along the common composite; the second hom maps it to restriction of g⁻¹G. |
| Composition identifications from the dependency | `upperStarComp`, `.inv ≫ ... .hom`, evaluated at G | Opened Defs: upstream upperStarComp has direction composite pullback → iterated pullback. This is the inverse of the node's c convention, so the displayed directions give precisely the node's κ. Its companion lowerStarComp is recorded by the same dependency. |
| Mayer–Vietoris restrictions on X | `rXU`, `rXV`, `rXIU`, `rXIV` with four canonical-map equality conjuncts | The first two equal pullback along U.ι,V.ι. The latter two are pullback along `X.homOfLE inf_le_left/right`, transported by the inverse composition isomorphism to G restricted directly to U∩V. |
| Mayer–Vietoris restrictions on Y | `rYU`, `rYV`, `rYIU`, `rYIV` with four canonical-map equality conjuncts | Same construction for g⁻¹G and the inverse-image opens; intersection inclusions use `g.preimage_mono`. |
| Two long exact sequences | `δX`, `δY`, two pair-map degree-zero injection clauses, and three `Function.Exact` clauses for each side and every q | Complete exactness at the pair, intersection, and next global group. Connecting maps are existential witnesses, as they are in the recorded etale_mayerVietoris dependency; the named restriction arrows are fixed, not existentially unconstrained. Products are finite two-summand direct sums of abelian groups. |
| Commutation of global-to-two-open square | First final `∀ q, ∀ x : Sheaf.H G q` conjunct, with both rYU/pU and rYV/pV equations | Both component squares; together they give the direct-sum square. |
| Commutation of difference-to-intersection square | Next final conjunct on a pair x | `rYIU(pU x.1) - rYIV(pV x.2) = pI(rXIU x.1 - rXIV x.2)`, with the same U-minus-V sign on both sides. |
| Commutation of connecting square | Last final conjunct | `δY q (pI q x) = cohomologyMap g G (q+1) (δX q x)`; includes the coefficient comparison missing from the original version. |
| Every square and every degree | All three final conjuncts quantify q : ℕ | Includes all repetitions in the long exact sequences, including degree zero and the shift to q+1. |

The existential map families preceding the equalities name the explicit arrows without
introducing definitions. They add no assumptions: each of the eleven families is fixed
by its equality to an existing construction. The two connecting families and full
exactness clauses exhibit the two Mayer–Vietoris sequences whose compatibility is claimed.
I read EtaleMayerVietoris.lean in full: its arrows are right-derived restrictions and its
connecting family is existential. Its isomorphisms identify cohomology on the objects of
X's site with cohomology on the corresponding open schemes. The present statement uses
the recorded Ext/pullback encoding of those groups, with the same restriction and
U-minus-V conventions, as that dependency's docstring specifies.

Edge cases: U may be empty (then V=X), V may be empty, the intersection may be empty,
and X or Y may be the empty scheme. There is no nonemptiness condition. In particular,
when U is empty, restriction to U alone need not be injective: this explicitly disproves
the original injection clause for a nonzero degree-zero class. The repaired injection
is into the pair. The zero sheaf is allowed; all its groups are zero. Degree zero is
included by both injections and the q=0 exactness and square clauses. There is no
coefficient field, characteristic, separatedness, Noetherian condition, or finiteness
assumption. There is no index set here beyond the two opens. The shared scheme universe
and coefficient universe u+1 follow the recorded small-étale-site and cohomology-map
encodings; any two schemes in different universes can be placed in a common larger
universe. All universes and variables are explicitly bound; local compilation uses
relaxedAutoImplicit=false and autoImplicit=false.

Independent searches, with wording different from the first worker's:

- LeanFinder: `étale cohomology restriction connecting homomorphism naturality scheme map`
  returned eight scheme-presheaf naturality declarations (Scheme.Hom.naturality,
  appLE_map, map_appLE, etc.), not long-exact-sequence pullback compatibility.
- Loogle: `"MayerVietoris"` returned twelve one-site square, sheaf-condition and
  short-complex declarations. I opened Mathlib's SheafCohomology/MayerVietoris.lean:
  its toBiprod, fromBiprod, δ and sequence_exact are for a single site and square,
  not a comparison under a scheme morphism.
- LeanSearch: `sheaf cohomology Mayer Vietoris naturality pullback` was unavailable
  (service Internal Server Error); this is an unavailable search, not a negative result.
- `rg` on upstream WeilConjectures/SixFunctors/Etale, Mathlib's
  SheafCohomology/MayerVietoris.lean, and the project's Etale modules for
  `MayerVietoris|mayerVietoris|cohomologyMap.*comp` found the landed one-scheme
  Mayer–Vietoris statement, Gabber's naturality of coefficient short-exact-sequence
  Ext classes, and pullback-related special cases, but no theorem with this statement.
  The pro-étale adic MayerVietoris module concerns a different site and coefficients.
  The declaration name is absent from the upstream names index. Existing upperStar,
  upperStarComp, cohomologyMap, Sheaf.H, Sheaf.H.map and homOfLE are reused throughout.

Mismatches found and repairs:

1. H3: `Function.Injective (rU 0)` is false for U empty; changed to injection of the
   two-component restriction map, for both X and Y.
2. H3/H4: existential `rU`, `rV`, `rI` were unconstrained arrows, not restriction and
   difference maps. Replaced them by named component maps each explicitly equal to
   the recorded pullback construction and its composition transport. Differences
   are the literal U-component minus V-component.
3. H3: the exactness clause after δX was missing, and Y had no exactness clauses.
   Added all three positions for both sequences, with degree-zero injections.
4. H3: the target of δY used g_I⁻¹(G|I) without identification with (g⁻¹G)|I′.
   Changed it to the latter, and inserted the stipulated `Sheaf.H.map` of the
   canonical composition isomorphism into the vertical map pI (also pU,pV).
5. H3: only the connecting square was stated, despite the docstring claiming three
   clauses. Added the two restriction component squares and difference square.
6. H8/H9: supplied the copyright header, placed the module docstring after imports,
   and replaced the two-sentence theorem docstring by the node's five proof steps,
   including the cited resolution, unit, composition, and naturality dependencies.

The unchanged natural-language node is correct. The previous second-reading paragraph
is explicitly superseded and did not catch these faults. No hollow definition or
extra theorem was introduced; the sole theorem proof remains `by sorry`. There are
no private definitions, local instances, local notation, or let/show statement binders.
The node's lean.statement was regenerated verbatim from the final theorem signature.
The repaired module compiled locally twice with no errors or warnings (4.8 seconds
for the first repaired version); the delivery tool supplies the final server check.
