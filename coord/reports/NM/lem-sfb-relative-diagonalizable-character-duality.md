## Worker report

The new module `Sheaf.AlgebraicGeometry.RelativeDiagonalizableCharacterDuality` states
`AlgebraicGeometry.relative_diagonalizable_character_duality`. It has one named theorem,
whose whole proof is `sorry`, and no new definitions. The natural-language proof in its
docstring follows all nine proof steps of the item. No mathematical statement correction,
new node, or dependency-interface repair is needed.

Hypothesis and clause correspondence:

1. The nonzero commutative ring is `(A : Type u) [CommRing A] [Nontrivial A]`.
   Its base is the existing `Spec (.of A)`. The groups are `(M N : Type u)` with
   `[AddCommGroup M] [AddCommGroup N] [AddGroup.FG M] [AddGroup.FG N]`.
   `ringDiagonalizableGroup A M` is exactly the recorded Hopf spectrum of the finitely
   supported group algebra; no replacement group or Hopf structure is introduced.
2. Every S-group homomorphism is the first conjunct's arbitrary
   `f : ringDiagonalizableGroup A M ⟶ ringDiagonalizableGroup A N`. These are actual
   group-object morphisms in the slice, not arbitrary scheme maps or assumed Hopf maps.
3. `∃! χ : LocallyConstant (Spec (.of A)) (N →+ M)` gives the unique locally constant
   character homomorphism. For each x, the open U contains x, χ is constant there,
   and `(Over.pullback U.ι).map f.hom.hom` equals the pullback of
   `(ringDiagonalizableGroupMap A (χ x)).hom.hom`. The opens therefore cover S.
   By the recorded definition that monomial Hopf map sends e_n to e_(χ(x)(n)).
   Requiring x in U avoids a false uniqueness claim on an empty open. The separate
   local uniqueness clause quantifies over every x, every open U containing x and
   every v : N →+ M. If the restrictions of f and D(v) agree there, it concludes
   v = χ x. Thus uniqueness is explicit even for local presentations not supplied
   by the existential cover, and independent of the closed-immersion criterion.
4. The adjacent iff is exactly
   `IsClosedImmersion f.hom.hom.left ↔ ∀ x, Function.Surjective (χ x)`.
   The local uniqueness clause independently characterizes every value of χ, so
   the criterion adds no qualifier to the uniqueness assertion.
5. The second conjunct binds every fixed `u : N →+ M` and every base change
   `T : Over (Spec (.of A))`. Its `IsPullback` square uses the specified canonical map
   `ringDiagonalizableGroupMap A (QuotientAddGroup.mk' u.range)` into D(M), the
   structural map to the terminal object, D(u), and the identity section η of D(N),
   all after the same base change. This identifies the kernel as D(M/range(u)),
   i.e. D(coker u), with its prescribed inclusion. `IsPullback` is the actual
   scheme-theoretic kernel square in the slice, so nilpotents are retained.
6. The same conjunct states that D(range u) → D(N), defined by `u.rangeRestrict`,
   is a closed immersion. Its factorization equation specifies that the two monomial
   maps D(M) → D(range u) → D(N) compose to D(u). The representable D(range u) is
   an fppf sheaf. The domain of ηi is
   `(Subfunctor.range (yoneda.map ...D(u)...)).toFunctor`, the actual pointwise-image
   presheaf, whose object at a test scheme consists of morphisms lying in the range
   of D(u) on that scheme. The equation `ηi ≫ yoneda.map ...D(u.rangeRestrict)... =
   (Subfunctor.range ...).ι` fixes its embedding in D(N). Bijectivity of composition
   with ηi against every Type-u-valued fppf sheaf is exactly the sheafification
   universal property. Thus this is the fppf sheaf image, not merely a scheme image
   or an arbitrary isomorphism of objects. The factorization and monic embedding
   also determine ηi composed with `Subfunctor.toRange` to be the specified map to
   D(range u); that normalization follows by cancellation.
7. The third conjunct binds every `L : AddSubgroup M` and every base change T.
   `IsFppfGroupQuotient` is applied to the prescribed maps D(M/L) → D(M) → D(L).
   Its existing definition contains the kernel square, fppf local surjectivity,
   the sheaf condition for D(L), the canonical torsor comparison, and the pointwise
   coset coequalizer with its normalized universal arrow to that sheaf. In particular
   the quotient is the sheafification of the pointwise quotient, not the pointwise
   quotient itself. The torsor comparison in the reused definition is the canonical
   equivalent quotient presentation, with inverse (g,g') ↦ (g,g⁻¹g').
8. The quotient arrow is `Flat` and `Surjective`, i.e. faithfully flat as a scheme
   morphism. `LocallyOfFinitePresentation`, `QuasiCompact` and `QuasiSeparated` state
   finite presentation, following the definition in def-sbc-locally-finite-presentation.
   All these predicates concern the actual quotient arrow, not its structure map.
9. The universal T in both the second and third conjuncts is an arbitrary scheme
   over S. Thus the canonical kernel square, specified image embedding and image
   sheafification, and quotient maps and quotient sheafification remain those same
   constructions after any scheme base change. The original descriptions follow
   by T = S with its identity structure morphism and the canonical pullback isomorphism.
10. The fourth conjunct makes the ring-base-change identification explicit. B is any
    commutative ring, without a nontriviality or flatness hypothesis, and ρ is any
    `A →+* B`. The group isomorphisms e are natural in finitely generated P and every
    homomorphism v. The equation for their inverses and the first pullback projection
    specifies `Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom P ρ))`.
    This is coefficientwise a e_p ↦ ρ(a)e_p. It determines the canonical comparison,
    and its naturality includes the range, quotient and subgroup homomorphisms.
    Together with the arbitrary-T clauses it expresses base-change compatibility
    of every displayed kernel, image and quotient, including nonflat base change.
11. The final conjunct binds any two homomorphisms f,g and every geometric point
    `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of A))`.
    Equality of their pullback maps at every such point implies `f = g`, exactly
    geometric-fibre detection. Equality is of fibre morphisms, not just of Ω-points.
12. Torsion in M,N and nilpotents in A are allowed: there are no torsion-free,
    reduced, domain, connected, smooth, characteristic or field hypotheses on them.
    All variables and the universe u are explicit; `autoImplicit` is false.

Dependency declarations read and used:

- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`
  and `AlgebraicGeometry.Spec.map`.
- def-sfb-ring-diagonalizable-group:
  `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`,
  `AlgebraicGeometry.ringDiagonalizableGroup` and
  `AlgebraicGeometry.ringDiagonalizableGroupMap`. Both full definitions and their
  Hopf-spectrum implementation were read; the contravariant directions are retained.
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- def-pc-fppf-site: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `AlgebraicGeometry.Scheme.fppfPrecoverage` and `.fppfTopology`, with
  `Mathlib.CategoryTheory.Sites.Over`, `GrothendieckTopology.over`, for the big slice site.
  These are publicly provided by the imported quotient-interface module.
- def-weil-pbc-sheafification: `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `CategoryTheory.toSheafify`, and
  `CategoryTheory.sheafificationAdjunction`. The image clause states their defining
  universal property rather than requiring a separately chosen global sheafification
  functor for every small-valued presheaf on the large site. The quotient clause
  uses exactly this same universal property inside the existing quotient interface.
- def-sbc-locally-finite-presentation:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`, with the quasi-compactness and quasi-separatedness
  predicates giving the node's full finite-presentation condition.
- def-weil-flat-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` (its docstring includes the stalkwise equivalence).
- def-weil-geometric-point: `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`,
  with the recorded inline geometric-point convention; read also
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`.
- Added landed definition dependency **def-sfb-fppf-group-quotient-presentation**:
  `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`,
  `AlgebraicGeometry.IsFppfGroupQuotient`. This live Q95 definition node records
  that exact declaration with `existing: true`. Its statement and record were read
  alongside the complete declaration at AffineNormalQuotientGeometry.lean:60.
  Its arbitrary scheme base B, kernel square, local surjectivity, representable
  sheaf, normalized torsor isomorphism and coset-presheaf sheafification conditions
  are exactly the notion used in this statement. The separate theorem
  `affine_normal_quotient_geometry` is not used to state this item and its theorem
  node is not added to stmt_deps. The module import stays unchanged because the
  definition node records the same existing module and declaration.
- Mathlib's `CategoryTheory.Subfunctor.range`, `.toFunctor` and `.ι` provide the
  pointwise-image presheaf; `LocallyConstant` provides local character labels;
  `AddMonoidAlgebra.mapRingHom` gives coefficientwise base change.

Proof-dependency modules are imported as plain imports: GammaSpecAdjunction,
Pullbacks, TensorProduct.Maps, Spectrum.Prime.Topology, Morphisms.Affine,
Flat.FaithfullyFlat.Basic and .Algebra, Morphisms.QuasiSeparated,
Sites.LocallyBijective, Cover.Open, Gluing and IsAlgClosed.AlgebraicClosure.
The recorded closed-immersion, flatness and finite-presentation interfaces are
already public statement imports. The canonical fppf site and Precoverage are
provided by the quotient-interface import. The algebraic-only proof dependency
lem-sfb-subgroup-algebra-coset-presentation has no recorded module yet, so there is
no module to import for it; it is not needed to elaborate the present statement.

Edge cases checked mathematically before writing and again after compilation:
M = 0 or N = 0; u = 0 or u surjective; L = 0 and L = M; 2Z inside Z;
Z/4 with its subgroup 2Z/4; μ_p in characteristic p; nonreduced bases such as
k[ε]/ε²; disconnected bases with different local u; empty test schemes; nonflat
A → A/I and A → 0. In the local clause x ∈ U excludes empty opens. The empty
base change remains allowed in every other clause; the ring B has no Nontrivial
assumption. For geometric fibres, residue fields and algebraic closures can be
chosen in the common universe u, so the quantified condition is not vacuous.

Searches performed:

- `msearch.py ... leansearch "Character duality for diagonalizable group schemes over
  commutative rings and their fppf sheaf quotients"`: 8 hits including
  CharacterModule.surjective_of_dual_injective, AddChar.doubleDualEquiv,
  FDRep.char_dual and CharacterModule.dual. These concern module/Pontryagin or
  representation duals, not relative diagonalizable group schemes or fppf quotients.
- `msearch.py ... leanfinder "Homomorphisms of split diagonalizable group schemes
  over rings correspond to locally constant homomorphisms of character groups with
  fppf kernels images and quotients"`: 8 hits, headed by Rep.diagonalHomEquiv_apply,
  Rep.diagonalHomEquiv_symm_apply, Rep.diagonalHomEquiv, TannakaDuality.FiniteGroup
  and PreGaloisCategory declarations; none states this relative theorem.
- `msearch.py ... loogle "MonoidAlgebra, HopfAlgebra"`: 3 hits,
  MonoidAlgebra.instHopfAlgebra, .instHopfAlgebraStruct and .antipode_single.
  They construct Hopf data but do not state local character duality or fppf quotients.
- `msearch.py ... grep "diagonalizable|Diagonalizable|groupLike" AlgebraicGeometry`:
  0 Mathlib hits. Read the actual Group.Affine Hopf-spectrum construction separately.
- `rg -n "diagonalizable|Diagonalizable" lean/WeilConjectures`: no match.
  `grep -rn "lem-sfb-relative-diagonalizable-character-duality" lean/WeilConjectures`:
  no match. `rg` over lean/Sheaf found the existing ring construction, the field-only
  DiagonalizableGroup and MultiplicativeCharacterAntiduality modules, and field-only
  DiagonalizableQuotientCharacterKernel. Their full relevant statements were read:
  none includes arbitrary nonreduced rings or locally constant character maps.
- Searched `IsFppf.*Image|Is.*Sheafification|IsSheafification|image.*sheafification`
  in the group-scheme interfaces and Mathlib's sheafification/subfunctor files;
  found the usable existing IsFppfGroupQuotient and Subfunctor.range interfaces.
  Searched the upstream name index and live declarations for the proposed theorem
  name and found no existing declaration with that name.
- Read the live node, every statement dependency's record and its declaration and
  docstring, and the proof-dependency records. Read Conrad Appendix B.1 and Remark
  B.1.2 online at the node's source URL, printed pp.280--281. The current blueprint
  is literature/blueprint/latest; this is an auxiliary node, not a unit statement,
  as its existing blueprint.from record and accepted split report explain.

Validation of the initial version: `scompile.py NM lem-sfb-relative-diagonalizable-character-duality
<module>` passed both the sandbox and final-module compilation in 2.2 seconds each,
with no errors or non-sorry warnings. Only files in the assigned sandbox were written.
No new nodes, dependency modules, or STATEMENT-DISPUTED issue.
After the explicit local-uniqueness clause was added, scompile.py again passed both
checks (14.3 seconds sandbox, 5.9 seconds final module) with no errors or non-sorry
warnings. The initial delivery dry run passed; the final dry run is run again on
this updated exact statement before pushing.

## Second reading by NM

The dispatcher's instruction prohibits starting another agent; this section records
an explicit second self-reading, not an independent second worker's review. The
maintainer performs the independent review of this delivery.

I reopened the node and complete Lean statement. Checked the monomial-map directions:
u : N → M gives D(M) → D(N); mk' range(u) gives D(coker u) → D(M);
rangeRestrict gives D(range u) → D(N); L.subtype gives D(M) → D(L).
The kernel square ends at the identity section of D(N). The image is the range
subfunctor of D(u) on all test schemes; its embedding and sheafification unit are
pinned by the displayed equation. The quotient is the actual coset presheaf
sheafification through the already recorded quotient interface, not a second notion.
Flat plus surjective expresses faithful flatness; the three finiteness predicates
express finite presentation. All constructions occur under one arbitrary pullback
functor for each T. The coefficient-normalized family e is natural for every v,
including subgroup, range and quotient maps. The last clause compares actual
geometric-fibre morphisms and concludes equality of the group morphisms. The input
hypotheses are exactly nonzero A and finitely generated abelian M,N. There is no
reducedness, connectedness or flat-base-change restriction. No mismatch or statement
correction was found. On this reading, local uniqueness was made explicit: any
monomial presentation on an open containing x has character map χ x. This avoids
relying on uniqueness of a tuple that also includes the closed-immersion criterion.
The only dependency-list change from the original base is citation of the live
**def-sfb-fppf-group-quotient-presentation**, the definition node owning the reused
IsFppfGroupQuotient declaration. The theorem node in the returned delivery has
been replaced; the actual Lean module and lean record are unchanged.


## Repair of returned delivery 52dd47df11f3

H2 repaired exactly as requested: replaced the added theorem dependency
`lem-sfb-affine-normal-quotient-geometry` with the existing live definition node
`def-sfb-fppf-group-quotient-presentation` in stmt_deps and updated the dependency
entry above. No other node field changed relative to the returned sandbox version.
Compared with the current main node, the original eight dependencies are preserved
and only the definition node is added; the current main has no Lean record yet.
The prescribed deliver2.py wrapper rebases the delivery onto current main.

The Lean module remains byte-identical to the returned version, SHA-256
`78a34b2f7cb96ec4b783d8b1bf8d376e953233d09786aefb0a0007d338052db2`.
The raw lean record text also remains byte-identical (checked before and after
replacing the dependency); its sorted JSON SHA-256 is
`dd9c22b92e3343d834a3d2f80a6a7d93ce7db0dcf7881d5599197fa536be873b`.
The maintainer's independent immutable-head review accepted the mathematics and
requested only this dependency-ownership correction. The earlier self-reading is
identified as such above; it is not claimed to be an independent review.

Validation for this repair uses scompile.py, followed by deliver2.py --no-push
and the normal delivery command. No direct Git command or live source edit is used.
