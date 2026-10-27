## Worker report

The module `Sheaf.AlgebraicGeometry.LocalQuotientEvaluation` states
`AlgebraicGeometry.Scheme.Modules.local_quotient_evaluation`, with `sorry` as its
only theorem proof. The node is unchanged except for `lean`. There are no new
nodes, dependency repairs or statement corrections.

Source read: `literature/stacks-project/morphisms.tex`, labels
`lemma-relatively-very-ample-separated` (01VQ) and
`lemma-relatively-very-ample` (01VR), especially lines 9177–9204, from the local
projective witnesses to the associated global morphism, before its immersion
comparison. This is exactly the part of (2) implies (4) isolated by the node.
The module docstring follows all six accepted proof steps; no proof is attempted.

Hypotheses, clause by clause:

- Schemes Z and X are `{Z X : Scheme.{u}}`; g is `(g : Z ⟶ X)`.
  Quasi-compactness is `[QuasiCompact g]`. There is no finite-type hypothesis.
- N is `(N : Z.Modules) [N.IsInvertible]`, using the recorded scheme-module
  invertibility predicate, not a replacement line-bundle structure.
- The arbitrary set-indexed cover is `(J : Type v) (V : J → X.Opens)` and
  `hV : iSup V = ⊤`. No finiteness, nonemptiness or compactness hypothesis occurs.
- Z_j is `(g ⁻¹ᵁ V j).toScheme` and g_j is `g ∣_ V j`. N restricted to it is
  `N.restrict (g ⁻¹ᵁ V j).ι`. This is Mathlib's actual sectionwise restriction.
- The local modules are `E : ∀ j, (V j).toScheme.Modules` and their only property
  is `[hE : ∀ j, (E j).IsQuasicoherent]`. In particular they need not be finite
  type, locally free or coherent.
- `D j : TautologicalQuotient (E j)` supplies the normalized O(1) and tautological
  quotient already defined by the projective-bundle dependency. It is the datum
  representing those canonical objects, not an additional geometric hypothesis.
- Each `i j` maps Z_j to the relative Proj of the canonical symmetric algebra of
  E_j; `hi j` says `i j ≫ relProjHom = g ∣_ V j`, exactly that it is over V_j.
  `himm j : IsImmersion (i j)` imposes an immersion, not a closed immersion.
- The chosen twist isomorphism is `e j : (tensorPullback (i j)).obj (D j).line ≅
  N.restrict (g ⁻¹ᵁ V j).ι`. The isomorphism is data, preserving its choice.
- `localProjectiveQuotient` defines q_j as the dependency's `pulledQuotient`
  followed by `(e j).hom`. Thus it is exactly the pulled tautological quotient,
  with composition of tensor pullbacks and the given twist isomorphism. Its
  surjectivity follows from the dependency's pullback epimorphism clause and
  composition with an isomorphism; no arbitrary quotient map is assumed.

Conclusions and specified constructions:

- F is always the actual term `(pushforward g).obj N`. Mathlib's
  `pushforward_obj_obj` identifies its sections with N(g^{-1}W), and
  `pushforward_obj_presheaf_map` and `pushforward_map_app` give its restrictions.
  Scalar restriction is part of the definition `Scheme.Modules.pushforward`.
- Epsilon is precisely `(tensorPullbackSectionAdjunction g).counit.app N`.
  This is the uniquely section-normalized adjunction supplied by the recorded
  pullback dependency, whose unit is the actual section 1 tensor m.
- The first two conjuncts are `IsSeparated g` and `QuasiSeparated g`.
- Surjectivity of epsilon is `Epi ((tensorPullbackSectionAdjunction g).counit.app N)`.
  Epimorphism of module sheaves means local/stalkwise surjectivity, not
  surjectivity on all sections.
- Quasi-coherence of F is the witness `hF : ((pushforward g).obj N).IsQuasicoherent`
  in the final existential. This witness also allows forming the canonical
  symmetric algebra and projective bundle of F, without a duplicate definition.
- For each j the theorem supplies `b : F.restrict (V j).ι ≅
  (pushforward (g ∣_ V j)).obj (N.restrict (g ⁻¹ᵁ V j).ι)`.
  Its orientation is the inverse of the identification as written in the node.
  The equality `b.hom = localQuotientPushforwardRestrictionMap g N (V j)` fixes
  the canonical map; b is not an arbitrary isomorphism. This map is defined by
  transposing the restricted actual global counit. On a local section it is
  the sectionwise identification of N(g^{-1}W), by the normalized tensor and
  restriction adjunctions. It has the same restrictions and scalar actions.
- Alpha_j has the required target `F.restrict (V j).ι`. The equality defining
  alpha_j is the actual local `homEquiv` applied to q_j, followed by `b.inv`.
  Thus alpha_j is exactly its adjoint under the sectionwise identification.
- The displayed q_j equality is
  `q_j = (tensorPullback g_j).map α ≫ comparison.hom ≫ restrictFunctor.map ε`.
  `localQuotientPullbackRestrictionIso` gives the canonical intervening comparison
  from g_j^*(F|V_j) to (g^*F)|Z_j. It uses the existing tensor composition
  comparisons, `morphismRestrict_ι`, and the existing restriction/tensor comparison.
  The last arrow is the restriction of the actual global epsilon. The formula
  does not substitute an arbitrary local counit for that restriction.
- With quasi-coherent F, the theorem supplies its normalized datum DF and
  `∃! r, Classifies DF g N ε r`. By the recorded definition of `Classifies`,
  this includes r over X, an isomorphism `r^* DF.line ≅ N`, and equality of
  the pulled tautological quotient followed by this isomorphism with epsilon.
  Its `∃!` is uniqueness of r among quotient-classifying X-morphisms, not
  uniqueness among all X-morphisms and not uniqueness of a bare line isomorphism.

The three helper definitions belong to the local quotient/evaluation construction
of this node and are listed in `lean.declarations`. Their data are explicit
composites of existing maps, isomorphisms and Hom equivalences. They contain no
`sorry`, choice from an unspecified existence theorem, auxiliary axiom or
postponed well-definedness proof. No independent new notion is introduced.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSectionAdjunction` and
  `tensorPullbackSectionComp`, retaining the recorded explicit `tensorPullback`
  from `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`:
  `Scheme.Modules.exists_tensorPullbackAdjunction`, the normalized adjunction
  of the recorded pullback-adjunction node, used by the section-normalized API.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData`:
  `ProjectiveBundleQuotientGeometry.TautologicalQuotient`, `pulledQuotient` and
  `Classifies`. The full definitions and normalization were read.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`:
  `projective_bundle_quotient_geometry`. Its signature permits arbitrary
  quasi-coherent E, asserts separated projection and unique classification.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` (local rank-one trivializations).
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes Mathlib's
  `SheafOfModules.IsQuasicoherent`, the quasi-coherence clause needed from
  `pqf-def-coherent`; its finite-type conjunction is deliberately not assumed.
- `Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`:
  `Scheme.Modules.restrictFunctorIsoTensorPullback`, with its normalized unit
  equation `restrictFunctorIsoTensorPullback_unit`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and `.Immersion`:
  `IsClosedImmersion` and `IsImmersion`, particularly the latter notion of the
  dependency's two clauses; no assumption of closedness is imposed on i_j.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `.QuasiCompact`:
  `QuasiCompact`; `LocallyOfFiniteType` is not assumed.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `.Separated`:
  `IsSeparated`; `IsProper` is not assumed.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`.
- Proof imports/interfaces: `WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs`,
  `isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated`;
  Mathlib `IsSeparated.instQuasiSeparated`, `IsSeparated.instCompScheme`,
  `IsZariskiLocalAtTarget.iff_of_iSup_eq_top`; tensor-pullback composition and
  epimorphism preservation from the recorded left-adjoint API. Mathlib modules
  are already reexported by the statement imports. No import cycle is introduced.

Edge cases checked before writing and again against the final signature:

- Empty Z: the local quotients and evaluation are morphisms of zero sheaves;
  the unique empty-domain map classifies the quotient.
- Empty X and J empty: `iSup V = ⊤` forces X empty, hence Z empty; no accidental
  `[Nonempty J]` excludes this case. An empty cover cannot cover nonempty X.
- Empty V_j and E_j = 0: relative Proj of zero is empty, so a witness i_j forces
  Z_j empty. Surjectivity is then the correct vacuous sheaf condition.
- Infinite covers and non-quasi-compact X are permitted. The sole compactness
  condition is on g, not on X, Z, the cover, or the chosen local immersion.
- E_j may have arbitrary infinite generating sets; no finite-rank API is used.
- A non-quasi-compact local open immersion is allowed; separatedness of an
  immersion does not require its quasi-compactness.
- For g the identity and N = O_X, the evaluation is the canonical identity up
  to its normalized pullback identification; a one-element cover works.
- Any characteristic and universe u are allowed. Independent universe v for
  the indexing set introduces no smallness restriction on this open cover.

Searches actually run (all via the prescribed wrapper unless otherwise stated):

- LeanFinder: `A quasi compact morphism with local immersions into projective
  bundles has quasi coherent pushforward of an invertible module and surjective
  evaluation factoring the local quotient through its adjoint`. Eight hits:
  Proj structure-sheaf equations, `Proj.pullbackAwayιIso`, `Proj.awayMap_awayToSection`
  and `Proj.fromOfGlobalSections` restriction formulas. None states this theorem.
- Loogle: `AlgebraicGeometry.Scheme.Modules.pushforward, Epi`. Zero hits, with
  diagnostic `loogle: unknown identifier 'Epi'`; this query did not resolve Epi.
- LeanSearch: `Evaluation counit surjective for a line bundle locally defining
  immersions into projective bundles`. Eight hits: smooth-sheaf evaluation,
  dual-module evaluation, condensed-set counit, scheme residue evaluation and
  closed-immersion section/stalk surjectivity. No match for this theorem.
- Mathlib grep: `local.*quotient|evaluation.*surject|surject.*evaluation`, restricted
  to AlgebraicGeometry. Eight unrelated structure-sheaf, subscheme and
  localization hits, no match.
- Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for the node ID,
  `local_quotient_evaluation`, evaluation-surjectivity and projective-quotient
  terms. Existing `RelativeAmpleVeryAmple` gives only the later relative-ampleness
  theorem, omitting local adjoints and factorizations and imposing finite-type
  hypotheses in its first part. `RelativelyVeryAmple` is the existing notion;
  it does not state this evaluation theorem. Reused all existing quotient APIs.
- Exact `grep -rn lem-trf-local-quotient-evaluation lean/WeilConjectures`: no hit.
  Name-collision `rg` searches of both Lean roots and `dag/lean_names_upstream.json`
  for all four new full-name suffixes gave no hit.

Validation: the full module was compiled by `scompile.py` against the live server
library. Its sandbox and library compiles passed cleanly (3.5 and 3.6 seconds on
its first version). The final version explicitly imports the recorded dependency
modules too. Expected postponed theorem only: `local_quotient_evaluation`.
No statement is disputed and no node fault was found.

## Second reading by Q20

I reread the source, node and final module in a separate pass. This is a worker
self-check; the maintainer's independent review is still required by the brief.
The hypotheses match: qc g, invertible N, arbitrary open cover, arbitrary
quasi-coherent E_j, an immersion over V_j and the chosen twist isomorphism.
The conclusions match: separated and quasi-separated g, quasi-coherent g_*N,
surjective normalized evaluation, the actual local adjoint and its factorization,
and a unique quotient-classifying morphism including the line isomorphism.
I checked the directions of `b` and `b.inv`: b goes from restricted global direct
image to local direct image, so the adjoint is followed by b.inv. I also checked
all five factors in `localQuotientPullbackRestrictionIso`: they follow the
restriction square in the required direction and end in actual open restriction.
The extra b equality fixes the canonical identification rather than changing the
mathematical content. There is no hidden arbitrary map or assumption of the
factorization. The final existential witness hF is the quasi-coherence clause,
not a hypothesis. The local restriction isomorphisms use the recorded tensor
comparison; no second pullback notion is defined. No mismatch or correction was
found. Only the one main theorem is postponed; helper definitions have real data.
