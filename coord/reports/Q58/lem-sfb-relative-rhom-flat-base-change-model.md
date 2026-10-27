## Worker report

The module `Sheaf.Algebra.Homology.RelativeRHomFlatBaseChangeModel` states
`CochainComplex.relativeRHom_flat_baseChange_model`, with its sole proof `sorry`.
Its statement is the node's entire statement, including arbitrary coefficient maps and
additive degree-zero normalization. Source read: `literature/stacks-project/more-algebra.tex`,
Tag 0E1U, `lemma-compute-RHom-relatively-perfect`, statement and full proof, lines
22039–22109. The displayed termwise comparison gives the transition normalization
by evaluation on pure tensors. The final finite-presentation clause is intentionally
outside this node. No statement correction, disputed statement, dependency repair, or
new independent definition node is needed.

The helper definitions name the existing tensor inclusion, its functorial coefficient
map, ordinary termwise scalar extension, the recorded derived scalar extension, pure
tensors, exact scalar restrictions and the actual derived-to-ordinary counit. The
predicate `RelativeRHomFlatModelPair` and the structures
`RelativeRHomFlatBaseChangeComparisons` and `RelativeRHomFlatBaseChangeTransitions`
package this node's hypotheses/conclusions. They are interfaces for this very statement,
not additional mathematical notions. In particular no definition chooses any data from
the postponed theorem. The sole theorem asserts existence of all comparison data with
their normalization equations. Every helper is listed in `lean.declarations`.

Hypotheses, one by one:

- `R S : Type u`, `[CommRing R]`, `[CommRing S]`, `[Algebra R S]` introduce arbitrary
  commutative rings and the ring homomorphism. An algebra structure is exactly the
  specified homomorphism in the commutative setting. No nonzero condition is present.
- `hflat : RingHom.Flat (algebraMap R S)` is exactly flatness of that homomorphism.
- `K L : DerivedCategory (ModuleCat S)` are ordinary unbounded module derived objects.
- `hK : DerivedCategory.IsPseudoCoherent K` uses the recorded bounded-above finite-free
  definition verbatim; it does not assert perfectness or any property of L.
- `a b : ℤ`, `hab : a ≤ b` introduce the given Tor interval.
- `hL` quantifies over every `N : ModuleCat R` and every integer j outside the interval.
  Its object is the derived tensor of the exact derived restriction of L with N[0],
  and `IsZero` of its `DerivedCategory.homologyFunctor` is precisely the required
  vanishing. The restriction retains the underlying R-complex. All module, ring,
  coefficient-algebra and morphism sizes are governed by the same arbitrary universe u;
  it can be chosen large enough for any rings and modules involved. There is no smaller
  independent universe of test modules that could make the condition vacuous.

Conclusions, clause by clause:

- The first conjunct is existence of P,F satisfying `RelativeRHomFlatModelPair`.
  That predicate explicitly requires a bound m and zero P-terms above m, free and
  finitely generated P-terms, `Q(P) ≅ K`, two bounds for F, R-flat restricted F-terms,
  and `Q(F) ≅ L`. `Module.Free` together with `Module.Finite` is finite freeness.
  Flatness is the existing `Module.Flat`, equivalent to preservation of exact sequences.
- The second conjunct quantifies over *any* such P,F and every pair of representation
  isomorphisms eP,eF. Thus the subsequent assertions are not limited to models chosen
  by the theorem's existence proof.
- E is exactly `CochainComplex.moduleHomComplex P F`, the recorded module-valued total
  Hom complex. Its existing differential is d_F h - (-1)^n h d_P; it is never replaced.
- `finiteSum` is an S-linear equivalence of each E^n with the direct sum indexed by p
  of linear Hom(P^p,F^(p+n)). `finiteSum_projection` identifies *every coordinate* with
  the existing cochain coordinate, rather than allowing an unrelated linear equivalence.
  Given the bounds of P,F, only c-n ≤ p ≤ min(m,d-n) can contribute; hence these are
  precisely the finite sums in the node, including empty sums.
- `boundedBelow`, `flat`, `represents` say E is bounded below, termwise R-flat, and
  its localization is isomorphic to `(ordinaryModuleDerivedInternalHom S).obj (op K,L)`.
- `T : CommAlgCat R` ranges over all homomorphisms R→T. Its ring is S tensor_R T;
  `relativeRHomScalar` is the canonical inclusion S→S tensor_R T.
  `relativeRHomDerived T` is exactly the recorded derived extension along that map.
  Thus its values on K,L are K_T,L_T from the node.
- The project uses left ordinary scalar extension `(S tensor_R T) tensor_S C`.
  `relativeRHomTensor T` is that termwise functor on the *original* complex C.
  Its canonical balancing with C tensor_R T sends `(s tensor t) tensor x` to sx tensor t,
  and its inverse sends x tensor t to `(1 tensor t) tensor x`. These are ordinary tensors,
  with no K-flat replacement hidden in `relativeRHomTensor`. Their S tensor_R T action
  is exactly the one in the node. `relativeRHomPure T C n s t x` names that pure tensor.
- `sourceIso`, `targetIso` identify Q(P_T), Q(F_T) with K_T,L_T. Their normalization
  equations use `relativeRHomCounit` composed with the given eP,eF; they cannot be
  arbitrary representative identifications.
- `homIso` is a chain **isomorphism**, not merely degreewise isomorphism or quasi-isomorphism.
  `homIso_pure`, at s=s'=1, reads precisely `(h tensor t)(p tensor u)=h(p) tensor tu`.
  The general s,s' formula includes all S-linear balancing relations. Pure tensors
  generate each term, so it fixes this chain map uniquely.
- `targetRepresents` supplies the Hom-model representation after base change.
  The real definition `relativeRHomBaseChangedIso c T` is exactly
  `Q.mapIso (c.homIso T) ≪≫ c.targetRepresents T`; this is the induced derived
  isomorphism E tensor_R T ≅ RHom over S tensor_R T.
- `homologyIso T` is the claimed additive isomorphism at H⁰. Its normalization says
  that a cycle carried by `homIso` to `Cochain.ofHom f` maps to
  `(sourceIso T).inv ≫ Q.map f ≫ (targetIso T).hom`. Every zero cocycle of Hom is a
  chain map, so this fixes the additive identification on all classes, not just on
  selected cochains.
- For each algebra map v:T→U, `change` is a chain map into exact scalar restriction.
  `change_pure` is h tensor t ↦ h tensor v(t), and also supplies these maps on P,F.
  They are uniquely fixed by the formula; they are not arbitrary comparison maps.
- `sourceUnit_universal` and `targetUnit_universal` spell out the universal-arrow
  characterization of derived scalar extension (bijectivity on every target Hom).
  The units' normalization identifies them with the localized coefficient maps on
  P,F via the *canonical* exact-restriction factorization and sourceIso,targetIso.
  Consequently these units give precisely the canonical iterated-tensor identifications.
- `transition` is the scalar-extension square on morphisms: if z' is the coefficient
  image of a degree-zero cycle z, then extending its derived morphism is its H⁰ image.
  The equality is expressed with the universal units, which determine the scalar
  extension of the morphism uniquely. Every class has a cycle representative; the
  chain map preserves cycles. This is the full cohomology-map assertion, not a condition
  only on a subset of classes.
- `change_identity` and `change_composition` state identity and composition on every
  element. Heterogeneous equality only accommodates the equal underlying modules
  carrying different syntactic restricted actions; it drops no equation. Together with
  the normalized units and transition square these give the comparisons' stated coherence.
- No finite presentation of R→S, pseudo-coherence or finite generation of L, flatness
  of R→T or T→U, boundedness below of P, or Noetherian assumption is present.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `RingHom.flat_algebraMap_iff`;
  `Mathlib.RingTheory.Flat.Basic`: `Module.Flat` and its exactness/injectivity equivalences.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`,
  `HasDerivedCategory`; `DerivedCategory.HomologySequence`: `homologyFunctor`.
- `Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison`:
  `AlgebraicGeometry.relativeDualizingDerivedExtension` and
  `AlgebraicGeometry.relativeDualizingExtensionCounit` (full signatures and constructions).
  They are the recorded canonical K-flat extension and counit, reused without modification.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, the recorded ordinary presentation
  of the generic ringed-site RHom from `def-pur-derived-internal-hom`.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`, including its complete finite-free model predicate.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`, ordinary ModuleCat
  presentation of complexes on the one-object site.
- `WeilConjectures.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex`, including its actual module-valued terms and differential.

All stated proof dependencies are imported without `public`: bounded projective models,
projective-module flatness, transitivity/base change of flat modules, bounded flat K-flatness,
flat opcycles, finite-product flatness, projective modules, the one-point projective Hom
computation, bounded-above K-projectivity and the derived-Hom bijection. The proof dependency
`lem-sfb-flat-algebra-derived-module-tensor-exchange` currently has neither a Lean record
nor a Mathlib match, so there is no module to import for it. It is only a proof dependency;
no object or interface from that unstated theorem is used to type this statement.

Edge cases checked before and during writing:

- Zero ring, zero K or zero L: no Nontrivial/Nonempty basis condition; rank zero is allowed.
- Empty degreewise sum: there is no nonempty-index condition, and the flat zero module is allowed.
- Negative and zero interval endpoints, a=b, arbitrary shifts: all indices and bounds are ℤ.
- P unbounded to the left, L not pseudo-coherent, R→S not of finite presentation: none excluded.
- Non-flat quotient base change (e.g. ℤ→ℤ/2), identity maps and composites: no flatness binders
  occur on coefficients, and both identity/composition equations are explicitly retained.
- Tensor orientation: substituting s=s'=1 in `homIso_pure` gives the node's exact formula;
  arbitrary s,s' ensures the canonical S tensor_R T linear action as well.
- Every comparison datum occurs in the conclusion, and no def extracts it by choice from sorry.

Searches actually run (via msearch.py with this group/item, and read-only rg):

- LeanFinder: `Derived Hom base change bounded above finite free complex bounded relatively
  flat complex`. Eight hits, headed by flat/faithfully-flat stability under base change and
  exact extension functors; no RHom-model statement.
- Loogle: `CochainComplex.moduleHomComplex, ModuleCat.extendScalars`. Zero hits; remote
  service does not know the project's `CochainComplex.moduleHomComplex` name. This is
  not evidence that the project lacks it; its recorded source was read and reused.
- Mathlib grep: `HomComplex|baseChange`, subdirectory `Algebra/Homology`. Twenty-five hits,
  mainly HomComplex, K-projectivity and HomComplexShift; no relative flat RHom base change.
- LeanSearch: `Derived Hom from pseudo coherent complex into relatively flat bounded complex
  commutes with arbitrary base change`. Eight hits, including ordinary flat base change,
  IsBaseChange linear Hom maps and exact derived functor factorization; none states this node.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for moduleHomComplex,
  ordinaryModuleDerivedInternalHom, relativeDualizingDerivedExtension and tensor/Hom base
  change found the reused interfaces and older perfect-source sheaf-site statements.
  Their bounded perfect-source hypotheses or sheaf presentations are different from this
  bounded-above pseudo-coherent-source ordinary-module theorem. Exact node-id search in
  `lean/WeilConjectures` found no declaration. Searches for the new declaration/helper names
  in both source trees and `dag/lean_names_upstream.json` found no collision.

Validation: all compiler calls use the prescribed scompile.py server wrapper, module mode,
with the unchanged 60-second limit. The final complete file compiled as both sandbox and
library module, clean apart from the expected sorry warning (roughly 15 seconds each).
The initial expensive equality encoding was repaired by keeping shared constructions as
named definitions and expressing coherence on underlying elements with HEq. No global build,
shared-source edits, direct Git command, launcher edit, or extra agent was used.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
