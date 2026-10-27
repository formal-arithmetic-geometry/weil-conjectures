## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveQuotientComparison` states
`AlgebraicGeometry.ProjectiveBundleQuotientGeometry.projective_quotient_comparison`.
This is the single postponed theorem. Four auxiliary definitions spell out parts of
this same comparison statement: `restrictedLineQuotient`, `inducedLocalLineQuotient`,
`comparisonLineMap`, and the proposition `HasQuotientOpenComparison`. Their data are
explicit; none uses sorry, an arbitrary-map parameter in place of a canonical map,
or a choice from an existence statement. The theorem has the node's six proof steps
in its docstring. The item's existing statement, dependencies and proof are unchanged.
No new nodes, dependency repairs or statement correction are needed.

Source read: `literature/stacks-project/morphisms.tex`, lines 9146--9243,
`lemma-relatively-very-ample`, Tag 01VR, specifically the comparison in (2) implies (4).
The node isolates its arbitrary-quotient comparison argument; the surrounding lemma's
quasi-compactness is used for its evaluation origin and quasi-coherent pushforward,
not for this comparison. The node's explicit local-frame and local-ring argument
applies without it. The projective-bundle classification data and theorem were read
in their current landed source modules.

Hypothesis and clause correspondence:

- Schemes Z and X, and their morphism g: `{Z X : Scheme.{u}} (g : Z ⟶ X)`.
- F quasi-coherent: `(F : X.Modules) [F.IsQuasicoherent]`.
- N invertible: `(N : Z.Modules) [N.IsInvertible]`, the recorded scheme-module predicate.
- The actual tensor quotient: `(q : (tensorPullback g).obj F ⟶ N) [Epi q]`.
  Epi is the module-sheaf surjectivity convention, not sectionwise surjectivity.
- The classifying map r: `r` into the relative Proj of the canonical symmetric
  graded algebra, with `hr : Classifies D g N q r`. D is a normalized tautological
  quotient datum, not an extra geometric property of F. The dependency theorem
  supplies such data, with its exact chart and generator normalization.
- The indexed covering: `(J : Type v) (V : J → X.Opens) (hV : iSup V = ⊤)`.
  Its index universe is independent; no finite or nonempty-index requirement is added.
- Z_j and g_j are literally `(g ⁻¹ᵁ V j).toScheme` and `g ∣_ V j`.
- E_j and alpha_j: dependent module family E with `[∀ j, (E j).IsQuasicoherent]`,
  and `α j : E j ⟶ (tensorPullback (V j).ι).obj F`.
- The restricted q uses `restrictedLineQuotient`: inverse composition comparison
  for g_j and V_j inclusion, equality `morphismRestrict_ι`, forward composition
  comparison for Z_j inclusion and g, then pullback of q. Every comparison comes
  from the dependency's section-normalized tensor adjunction.
- `inducedLocalLineQuotient` is exactly `(tensorPullback g_j).map alpha_j`
  followed by that restricted q. `hqi` asserts its surjectivity for every j.
- DE_j is normalized tautological data for P(E_j); `hi` states that i_j classifies
  exactly that induced quotient with line the restriction of N. `himm` states that
  every i_j is an immersion, using Mathlib's locally closed immersion predicate.
- For every j the conclusion gives `HasQuotientOpenComparison`. This is a proposition
  defined by explicit existential binders, not a new projective-bundle notion.
  It supplies normalized tautological data for P(F restricted to V_j), an inclusion
  into P(F), an `IsPullback` square, and a line isomorphism with the displayed
  quotient equality. These express the base restriction identification used in
  the node's phrase r restricted to Z_j, rather than substituting an arbitrary map.
- The existential `restriction` classifies the restricted q and satisfies
  `restriction ≫ inclusion = (g ⁻¹ᵁ V).ι ≫ r`.
- P_j and p_j are the relative Proj and `relProjHom` of the canonical symmetric
  graded algebra on `(tensorPullback V.ι).obj F`. The existing tensor-pullback
  quasi-coherence instance permits this restriction without an extra hypothesis.
- `comparisonLineMap tautological E α` is exactly p_j pullback of alpha_j followed
  by the tautological quotient. There is no surrogate beta_j parameter.
- `locus` is a scheme open, with the biconditional `∀ y, y ∈ locus ↔
  Function.Surjective ((RingedSpace.moduleStalkFunctor ... y).map beta_j)`.
  Thus openness is asserted for precisely the node's set, without asserting
  openness of an arbitrary surjectivity locus with arbitrary target.
- `comparison` is h_j from that open into P(E_j). Its `Classifies DE` predicate
  uses the restriction of the tautological line and the pullback of beta_j,
  precomposed with the canonical composition comparison to its correct domain.
  This states that h_j is classified by the indicated quotient, not just a map
  with the right commuting scheme diagram.
- `lift` is the required tilde r_j. The equalities `lift ≫ locus.ι = restriction`
  and `lift ≫ comparison = i` give both factorization identities.
- The last conjunct `IsImmersion r` is the global conclusion.
- No quasi-compactness, finite type, finite presentation or local-freeness of g,
  F or E_j is assumed. The local invertibility requirement is solely on N and
  the tautological line, as in the node.

Dependency declarations used, with full signatures/docstrings inspected:

- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSectionComp` and
  `tensorPullbackSectionAdjunction`; this module publicly reexports the real
  tensor construction, and defines the section-normalized composition comparisons.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  inherited through the projective-bundle data import.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData`:
  `ProjectiveBundleQuotientGeometry.TautologicalQuotient`, `pulledQuotient`,
  `Classifies`; its canonical symmetric algebra and relative Proj are reused.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, publicly reexported by the data module.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and `.Immersion`:
  `IsClosedImmersion`, `IsImmersion`, `isImmersion_iff_exists`, `IsImmersion.of_comp`.
  The immersion module is public; its imports expose the recorded closed-immersion
  notion as well as the immersion clause of the same dependency node.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`:
  `projective_bundle_quotient_geometry`. Its data-only module is public, while
  the theorem module is imported for the proof dependency, avoiding exposing
  its private proof imports to downstream consumers.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded interface publicly
  exposes `SheafOfModules.IsQuasicoherent` (the clause used here), not the stronger
  finite-type conjunction. It is inherited through ProjectiveBundleQuotientData.
- `Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent`:
  `Scheme.Modules.isQuasicoherent_tensorPullback`, with
  `tensorOrdinaryPullbackIso`; the already landed support instance is publicly
  imported to form the canonical projective bundle of F restricted to V.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `RingedSpace.moduleStalkFunctor`, the actual linear stalk-map functor.
- Proof imports: `WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`
  (`exists_tensorPullback_stalk_iso`); `Mathlib.Topology.Sheaves.LocallySurjective`
  (`TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks`).
  The other proof leaves are exposed by the public immersion import:
  `LocallyRingedSpace.Hom`, `IsOpenImmersion`, its `lift`, `lift_fac`, `lift_uniq`,
  and `IsZariskiLocalAtTarget.of_range_subset_iSup`. Their sources were inspected.

Edge cases checked before writing: an empty covering index forces X empty and hence
Z empty, and the conclusion remains correct; an empty Z works with zero quotients
of the unique empty-scheme module; F=0 permits a surjection onto an invertible N
only on an empty Z; E_j=0 similarly forces Z_j empty under the surjectivity
hypothesis. Empty V_j are allowed. Infinite-rank F and E_j are allowed, and openness
is justified by the rank-one target and a local right inverse, not finite generation
of the source. Non-quasi-compact g is retained. Alpha_j need not be injective or
surjective. The surjectivity locus can be empty or the full projective bundle.
All universes and implicit variables are bound explicitly with autoImplicit and
relaxedAutoImplicit disabled.

Searches actually run (msearch log in sandbox/searches.jsonl):

- leanfinder: “The open surjectivity locus of a map into the tautological line of a
  projective bundle compares line quotient classifying morphisms and detects
  immersions”: 8 hits, chiefly `Proj.awayι`, `Proj.pullbackAwayιIso`,
  `Proj.fromOfGlobalSections` and open-immersion helpers; no arbitrary-module
  relative projective quotient comparison theorem.
- loogle: `AlgebraicGeometry.IsImmersion, AlgebraicGeometry.Proj`: 0 hits.
- Mathlib grep: `projectiveBundle|ProjectiveBundle|[Ii]mmersion.*quotient|quotient.*[Ii]mmersion`
  in AlgebraicGeometry: 3 hits in IdealSheaf/Subscheme and Morphisms/ClosedImmersion;
  these concern ideal quotients, not the comparison here.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for projective quotient, immersion
  and quotient, surjectivityLocus and surjectiveLocus: related projective-bundle
  geometry and relative-ample consumers, no exact comparison statement or helpers.
- grep for the item's blueprint id in `lean/WeilConjectures`: no hits.
- rg for the proposed declaration names in both source roots and
  `dag/lean_names_upstream.json`: no collisions.

No STATEMENT-DISPUTED flag or node fault. No helper theorem has been added.

## Second reading by Q15

Self-check only: this dispatcher-started worker was explicitly instructed not to
start another agent; independent review belongs to the maintainer. Reopened the
node and module and checked the clause correspondence above. In particular, beta_j
is the actual composite, U_j is exactly its stalk-surjectivity locus, h_j classifies
its restricted quotient, and the lift records both identities. The local quotient
uses the correct direction of the normalized composition isomorphisms. Restriction
of r is tied to its original global morphism by the quotient-compatible cartesian
base identification. The module assumes no finite generation or quasi-compactness.
The auxiliary proposition merely packages these conclusions; the only theorem
proof is sorry. No mathematical statement change was made.
