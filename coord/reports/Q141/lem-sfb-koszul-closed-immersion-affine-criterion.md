## Worker report

The module states two theorems, with `sorry` as each entire proof, for the unchanged
node. It introduces no definitions or additional nodes. Source read in full:
`literature/stacks-project/divisors.tex`, definition-regular-ideal-sheaf (063D),
and lemma-regular-ideal-sheaf-scheme (063G), including the exact-sheafification
argument. The principal refinement follows the node's proof, using Tag 01I3 and
flat base change (062H).

Hypothesis and clause correspondence for
`AlgebraicGeometry.koszulClosedImmersion_affine_criterion`:

- Schemes and a closed immersion: `{T W : Scheme.{u}} (a : T ⟶ W)
  [IsClosedImmersion a]`. The defining ideal is precisely `a.ker`, not an
  independent ideal or a chosen isomorphic substitute.
- Locality along a(T): `∀ t : T, ∃ N : W.Opens, a t ∈ N ∧ ...`.
- Finitely many sections: `∃ (r : ℕ) (s : Fin r → Γ(W, N)), ...`;
  there is no positive-length restriction.
- These sections generate the ideal sheaf on N: for every affine subopen
  `V : W.affineOpens` with `hVN : V.1 ≤ N`, the ideal spanned by the
  restrictions `W.presheaf.map (homOfLE hVN).op (s i)` equals `a.ker.ideal V`.
  This is exactly sheaf generation: on affine subopens, both the ideal sheaf
  and the image ideal of the finite generating map are quasi-coherent;
  associated sheafification identifies sheaf surjectivity with surjectivity
  of the corresponding module map. Affine subopens form a basis of N.
  This avoids the incorrect assertion of global section surjectivity on a
  non-affine N. The two global-to-local constructions are not additional data.
- Germ regularity is required at every `w : W` with `hw : w ∈ N`, using
  `RingTheory.Sequence.IsKoszulRegular
  (fun i ↦ W.presheaf.germ N w hw (s i))`.
  In particular points outside a(T) are included.
- The equivalence is `↔`, not a one-way implication.
- Arbitrarily small neighborhoods: `∀ (t : T) (O : W.Opens), a t ∈ O → ...`.
- The affine open is `U : W.affineOpens`; membership and containment are
  `a t ∈ U.1 ∧ U.1 ≤ O`. B is the canonical section ring `Γ(W, U.1)`,
  canonically presenting U as its spectrum.
- The ideal J is `a.ker.ideal U`; the sequence `f : Fin r → Γ(W, U.1)`
  is Koszul-regular and `Ideal.span (Set.range f) = a.ker.ideal U`.
- The inverse image is the actual open subscheme `(a ⁻¹ᵁ U.1).toScheme`.
  The existential isomorphism `e` identifies it with Spec(B/J), and the
  equation `(a ∣_ U.1) ≫ U.1.toSpecΓ = e.hom ≫ Spec.map ...` makes
  that identification over U (using its canonical affine spectrum map).

The final affine-specialization clause is
`AlgebraicGeometry.koszulClosedImmersion_principal_refinement`:

- `(A : Type u) [CommRing A] (I : Ideal A)` gives the exact quotient
  immersion `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))` from
  Spec(A/I) to Spec(A).
- `hregular` is the affine finite Koszul-generator condition of the first
  theorem (choosing the whole ambient open). This is equivalent to the
  local condition by that theorem. The omitted quotient-isomorphism conjunct
  follows automatically for this closed immersion, with the same kernel ideal;
  it is not a separate assumption.
- For every `t` and every `O` containing its image, the witness `h : A`
  obeys `h ∉ (... t).asIdeal` and `PrimeSpectrum.basicOpen h ≤ O`.
- The list is `f : Fin r → Localization.Away h`; it is Koszul-regular,
  and its span is exactly `I.map (algebraMap A (Localization.Away h))`,
  the extended ideal I A_h.
- `eU` identifies the actual D(h) open subscheme with Spec(A_h), and
  its equation identifies its structural map with Spec of the localization
  homomorphism. `eT` identifies the actual inverse image with
  Spec(A_h / I A_h), and its equation identifies the restricted immersion
  with Spec of the quotient homomorphism, over D(h).
- No Noetherian, finite presentation, regular-sequence, proper-ideal,
  or positive-length assumption appears in either theorem.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, `Spec.map` (all statement dependencies).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (statement dependency; its affine
  property also supplies the proof's affine-quotient input).
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`,
  `Scheme.IdealSheafData.ideal` (statement dependency, publicly available
  through ClosedImmersion). `Hom.ker_apply` identifies its affine ideals
  with the kernels of the actual section maps.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular` (the declaration in the dependency's
  `lean.declarations`, defining positive Koszul homology vanishing).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, used
  through the canonical open-subscheme constructions in Restrict and the
  affine opens supplied by the imported scheme modules.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`,
  with its commutative-ring and algebra structures from
  `Mathlib.RingTheory.Localization.Away.Basic` (statement dependency).

Proof imports include the recorded tilde finite-limit preservation, tilde
adjunction, module stalk exactness, localization flatness, Koszul regularity
under flat base change, and affine module basic-open localization modules.
The other Mathlib proof inputs are already exposed by these dependencies
(affine basis, affine closed-immersion criterion, free tilde modules,
prime-localized stalks, distinguished opens and quasi-coherent ideals).
No unavailable proof interface is assumed as a hypothesis.

Edge cases checked before drafting:

- Empty T: the first equivalence and the principal-refinement conclusion are
  vacuous, including I = top.
- r = 0: `Fin 0` is allowed; span of its range is zero, and the Koszul
  complex has no nonzero positive terms. This includes identity immersions.
- A unit equation: it has contractible Koszul complex and defines the empty
  subscheme. No properness of the generated ideal is imposed.
- The one-term sequence (0) over a nonzero field is not Koszul-regular;
  the formula does not conflate ordinary ideal generation with Koszul regularity.
- The zero ring has empty spectrum; no unwanted Nontrivial assumption occurs.
- Non-Noetherian rings and schemes are retained. All scheme and coefficient
  rings use the explicitly bound universe u, and all point/list variables
  are explicitly bound. There is no implicit universe equality restriction.

Searches for existing statements:

- msearch.py leanfinder: "A closed immersion is locally Koszul regular if and
  only if on arbitrarily small affine neighborhoods its ideal has Koszul
  regular generators" — 8 hits, ordinary smoothness/closed-immersion
  declarations, no Koszul affine equivalence.
- msearch.py loogle: `"Koszul", "IsAffine"` — 0 hits.
- msearch.py grep: `Koszul|koszul`, AlgebraicGeometry — 0 Mathlib hits.
- msearch.py leansearch: "An ideal sheaf locally generated by sections whose
  germs are Koszul regular has arbitrarily small affine Koszul regular
  presentations" — 8 hits, including IdealSheafData.ideal and
  IsAffineOpen.mem_ideal_iff; none is the claimed equivalence.
- rg in lean/WeilConjectures and lean/Sheaf for Koszul affine/local criteria
  found KoszulRegularAffineRefinement and CotangentPresentation.IsKoszulImmersion.
  The former refines already given affine generators; it does not compare
  sheaf/germ regularity with affine regularity. The latter is the finite-affine
  chart predicate, not the sheaf/germ condition or the principal refinement.
  Neither supplies this statement. No new named predicate is needed here.
- rg for this node id in lean/WeilConjectures found no declaration.
  DAG searches found related chart/near-point definitions; their recorded
  source declarations were read. No private copy of either is introduced.

No statement correction, new nodes, dependency repair, or statement dispute.

## Second reading by Q141

I reread the node and both signatures, clause by clause, after drafting; this
is the worker's own second pass, with the independent delivery review left to
the maintainer as instructed by the dispatcher. The first theorem explicitly
keeps every-point germ regularity, arbitrary prescribed opens, the same ideal,
and the quotient isomorphism over U. The second theorem keeps the canonical
localization map, extended ideal, and quotient map over D(h). Generation is
checked on all affine subopens, so it means sheaf generation rather than the
stronger and false non-affine-global-section version. No mismatch was found.
The first compiler run identified namespace resolution for `.toScheme` and
`.ι` on a prime-spectrum open; these were replaced by the fully qualified
`Scheme.Opens.toScheme` and `Scheme.Opens.ι`, with the ambient spectrum
explicitly supplied: its underlying space alone does not determine a scheme.
No mathematical change resulted.
