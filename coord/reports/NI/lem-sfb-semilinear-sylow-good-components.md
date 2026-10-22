## Worker report

Repair of independent stage-2 return ca314767d1bc. This is a Lean-statement delivery,
not a redelivery of the superseded stage-1 split. At the start of this retry the sandbox
contained only dispatcher metadata; there were no retained node/module/report files.
The node was therefore copied afresh from the current shared live source, which already
contains NJ's reviewed split. Its statement, proof, proof_deps, proof_origin,
mathlib_searches and split_report are preserved exactly. The only deltas are the lean
record and adding the already-landed definition def-per-admissible-finite-scheme-quotient
to stmt_deps. Neither the module nor the delivered node cites
lem-per-projective-finite-group-quotient.

The new module is lean/Sheaf/AlgebraicGeometry/SemilinearSylowGoodComponents.lean;
its sole declaration is AlgebraicGeometry.semilinear_sylow_good_components, with proof
sorry. There are no new definitions, new nodes, dependency repairs or statement changes.
Its docstring transcribes all thirteen steps of the current live proof and names their
current dependencies. The unavailable proof-only nodes lem-sfb-finite-quotient-normal-proper,
lem-sfb-finite-normal-ample-descent and lem-sfb-finite-quotient-generic-fields have no
Lean modules to import; their statements are not used as assumptions. All currently
recorded proof modules are imported non-publicly, unless already public statement imports.

Source read: ILO, Travaux de Gabber, Expose X 2.3 Step 2, diagram (2.c), printed p.151
(physical PDF page 157), and the continuation on printed p.152. The source describes the
Sylow constants quotient and the prime-to-ell alteration. The live node explicitly
selects good components so that the degree assertion holds at EVERY generic point of
the selected source, rather than only as a total generic degree. That convention is
retained. No statement fault or STATEMENT-DISPUTED issue was found.

Hypothesis-by-hypothesis rendering:

| Node hypothesis / object | Lean rendering |
| --- | --- |
| Fields e and K, finite field extension K/e | `(e K : Type u) [Field e] [Field K] [Algebra e K] [Module.Finite e K]` |
| ell prime and different from the characteristic of e | `hell : ell.Prime`, `hchar : ell ≠ ringChar e` |
| Finite group acting on K by e-automorphisms | `(G : Type v) [Group G] [Finite G]`, `ρ : G →* (K ≃ₐ[e] K)` |
| K^G/e purely inseparable | `hfixed : IsPurelyInseparable e (IntermediateField.fixedField ρ.range)` |
| B an e-scheme and Y a K-scheme | `b : B ⟶ Spec (.of e)`, `p : Y ⟶ Spec (.of K)` |
| B nonempty, normal, proper, finite type | `[Nonempty B] [IsProper b]` and `hBnormal`, which asserts `IsDomain` and `IsIntegrallyClosed` for every stalk; properness supplies `LocallyOfFiniteType b` and `QuasiCompact b` |
| B a finite disjoint union of integral schemes | `hBcomponents` gives finitely many opens `V : Fin n → B.Opens`, each `IsIntegral`, pairwise disjoint, covering B; each is consequently also closed |
| Y smooth and projective over K | `[Smooth p] [IsHProjective p]` |
| G acts on Y by e-automorphisms, semilinearly over K | `a : G →* Aut Y`, `hequivariant`, and `hbase`; the displayed equation uses `(ρ g⁻¹).toRingHom` because a left action on schemes induces the inverse-pullback left action on constants |
| h is a morphism of e-schemes | `hbase : h ≫ b = p ≫ Spec.map (CommRingCat.ofHom (algebraMap e K))` |
| h invariant, projective and surjective | `hinvariant`, `hhprojective : IsProjectiveBundle h`, `hhsurjective : Surjective h` |
| Every generic point of Y maps to a generic point of B with finite residue extension | `hhgeneric : ∀ y ∈ genericPoints Y, h y ∈ genericPoints B ∧ (h.residueFieldMap y).hom.Finite` |
| All subgroup quotients given, finite, invariant and with invariant structure sheaves | `Q : Subgroup G → Scheme`, `q : ∀ H, Y ⟶ Q H`, and `hquot : ∀ H, IsAdmissibleFiniteSchemeQuotient (a.comp H.subtype) (q H)` |
| These quotients categorical as scheme quotients | `hcat` quantifies over every target scheme T and every invariant f, asserting a UNIQUE r with `q H ≫ r = f` |
| These quotients geometric | `hgeom` asserts surjectivity on geometric points over each algebraically closed Ω and that equality of images is equivalent to membership in one H-orbit |
| The induced maps from the quotients to B | `d : ∀ H, Q H ⟶ B`, `hd : ∀ H, q H ≫ d H = h`; these name the unique descents supplied by hcat and hinvariant |
| Dense open meeting every component where Y/G to B is a finite universal homeomorphism | `hdense` gives a dense open V containing `genericPoints B`, and asserts `IsFinite` and `(topologically IsHomeomorph).universally` for the restriction of `d ⊤` |
| L an ell-Sylow subgroup in the stated order/index convention | `L : Subgroup G`, `hLorder : ∃ n, Nat.card L = ell ^ n`, `hLindex : Nat.Coprime L.index ell` |
| F = K^L and Q = Y/L | `F : IntermediateField e K`, `hF : F = IntermediateField.fixedField (L.map ρ)`; the quotient is `Q L` |

The existing admissible finite-quotient predicate is usable without an extra mathematical
hypothesis here. Its affine-orbit requirement follows from the stated hypotheses: choose
an affine neighbourhood of the image of an orbit; its inverse image under the FINITE
quotient is affine and contains that orbit. A finite surjection is a closed quotient map.
The ordinary point-fibre orbit condition follows from the geometric condition: the finite
residue extensions of two points in one fibre embed into a common algebraic closure of
the base residue field, where hgeom applies. The predicate's final clause is precisely
injectivity of q.app on each open and equality of its image with the invariant sections,
so it includes the entire invariant-structure-sheaf condition. The extra clauses hcat and
hgeom are written explicitly, since the predicate's signature alone does not contain them.
This uses the existing definition, rather than duplicating any invariant-section maps.

The chosen quotient presentations and their descents are data for the quotients already
assumed in the node. They impose no existence, normality, projectivity, degree, faithfulness
or freeness assumptions beyond the node. All choices of Q and q with the stated quotient
properties are allowed. By hcat the maps d are uniquely forced by hd; they are not arbitrary
replacements for a canonical map. Likewise hF is the equation introducing the named field
F, not an additional restriction on the fixed field. The theorem constructs sF and pins it
by the equation with q L, p, and the ACTUAL inclusion F.subtype into K.

Conclusion clause-by-clause:

| Node conclusion | Lean rendering |
| --- | --- |
| [F:e] finite and prime to ell | `Module.Finite e F ∧ Nat.Coprime (Module.finrank e F) ell` |
| K/F finite Galois | `Module.Finite F K ∧ IsGalois F K` |
| Its group is the image of L in Aut_e(K) | `F.fixingSubgroup = L.map ρ`; F.fixingSubgroup is exactly the e-automorphisms of K fixing F, canonically the F-Galois group, so this is equality of the actual image subgroup |
| Induced F-structure on Q | `∃ sF : Q L ⟶ Spec (.of F), q L ≫ sF = p ≫ Spec.map (CommRingCat.ofHom F.subtype)` |
| Qcirc open and closed | `U : (Q L).Opens`, `IsClosed (U : Set (Q L))` |
| Qcirc a union of irreducible components | `∃ C : Set (Set (Q L)), C ⊆ irreducibleComponents (Q L) ∧ (U : Set (Q L)) = ⋃₀ C` |
| Meets the fibre over every generic point of B | `∀ x ∈ genericPoints B, ∃ z : U.toScheme, (U.ι ≫ d L) z = x` |
| Qcirc normal projective over F | `IsDomain` and `IsIntegrallyClosed` on each stalk of U.toScheme; `IsHProjective (U.ι ≫ sF)` |
| Induced map to B projective surjective | `IsProjectiveBundle (U.ι ≫ d L) ∧ Surjective (U.ι ≫ d L)` |
| Every generic point maps to a generic point, with finite prime-to-ell residue degree | `∀ z ∈ genericPoints U.toScheme, ... ∈ genericPoints B ∧ ...residueFieldMap z...Finite ∧ Nat.Coprime (...residueDegree z) ell` |
| Ycirc the actual inverse image of Qcirc, clopen | the open is always `q L ⁻¹ᵁ U`, with `IsClosed ((q L ⁻¹ᵁ U) : Set Y)` |
| Restricted action is the actual L-action | `∃ aU : L →* Aut (q L ⁻¹ᵁ U).toScheme`, with `(aU g).hom ≫ inclusion = inclusion ≫ (a g).hom` for every g |
| Ycirc to Qcirc the finite quotient by L | `IsAdmissibleFiniteSchemeQuotient aU ((q L).resLE U (q L ⁻¹ᵁ U) le_rfl)`, followed by categorical uniqueness and geometric surjectivity/orbit fibres for this SAME restricted morphism |
| No requirement on omitted components | All degree and normal-projective assertions concern U.toScheme; none asserts prime-to-ell degrees on the complement |

Dependency declaration sources read and used:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.Algebra.Algebra.Defs: Algebra.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Morphisms.QuasiCompact: QuasiCompact; Morphisms.Proper: IsProper.
- Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism: AlgebraicGeometry.IsProjectiveBundle.
- Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap: AlgebraicGeometry.Surjective.
- Mathlib.Topology.Irreducible: irreducibleComponents; Mathlib.Topology.Sober:
  IsGenericPoint and genericPoints. The latter is the set of points whose singleton
  closure is an irreducible component, exactly the quantified generic points of the node.
- Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField,
  Scheme.Hom.residueFieldMap and Scheme.Hom.residueDegree. Finiteness is asserted
  separately because residueDegree defaults to zero for infinite extensions.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: AlgebraicGeometry.IsHProjective,
  the existing finite-projective-space convention; exposed by ProjectiveBundleMorphism.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: AlgebraicGeometry.IsFinite.
- Mathlib.CategoryTheory.MorphismProperty.Limits: MorphismProperty.universally;
  Mathlib.AlgebraicGeometry.Morphisms.Constructors: topologically;
  Mathlib.Topology.Homeomorph.Defs: IsHomeomorph.
- Sheaf.FieldTheory.FieldTower: FieldExtension.degree and its documented finite-extension
  Module.finrank convention. The signature uses Module.Finite and Module.finrank directly.
- Mathlib.FieldTheory.Galois.Basic: IntermediateField.fixedField and fixingSubgroup;
  Mathlib.FieldTheory.PurelyInseparable.Basic: IsPurelyInseparable.
- Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient:
  AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient, read both locally and with
  `scompile.py --source`; the live definition agrees. Its already-landed owning node
  is the sole added statement dependency.
- Mathlib.AlgebraicGeometry.Restrict: Scheme.Hom.resLE and the canonical open inclusions.

Edge cases checked before finalizing the statement:

- B empty is explicitly excluded by the source. Y empty is impossible by surjectivity of h;
  no unnecessary Nonempty Y hypothesis was added. A zero-sized component cover cannot
  cover the nonempty B. U empty is excluded by the generic-fibre meeting clause.
- Disconnected B and Y remain allowed. The quantified generic point ranges over every
  component of U, not a chosen one or the total degree. Omitted components are unrestricted.
- Nonfaithful constants and scheme actions remain allowed: only image subgroups enter
  the fixed fields and Galois-group conclusion. The subgroup L itself is never identified
  with the Galois group.
- Characteristic zero is allowed by IsPurelyInseparable (forcing the relevant extension
  trivial there). In positive characteristic only ell differing from it is assumed.
- Trivial G, trivial L, and ell not dividing the group order are allowed. The exponent in
  the Sylow order hypothesis can be zero. No freeness or separability of generic residue
  extensions was assumed.
- Fields and schemes share an arbitrary universe u, while the finite group has independent
  universe v. One may take u large enough for any given finite extension. Geometric tests
  use algebraically closed fields in the scheme universe, including algebraic closures
  of all residue fields; no smaller-universe vacuity is introduced.
- The inverse on ρ in hequivariant is needed: Aut multiplication composes scheme maps
  in the opposite order from pullback of functions. Fixed subgroups and fixed fields
  are unchanged by replacing g with its inverse.

Searches actually run:

1. msearch.py leansearch, query: `Let a finite group act semilinearly on a smooth
   projective scheme. A Sylow quotient has components of generic degree prime to the
   Sylow prime.` Result: 8 Sylow facts, including Sylow.isPretransitive_of_finite,
   Sylow.not_dvd_index and Sylow.isPGroup'; no theorem about these scheme components.
2. msearch.py leanfinder, query: `finite semilinear group action on a smooth projective
   scheme Sylow quotient components prime to ell residue degrees`. Result: 8 hits about
   arithmetic Frobenius and invariant ring residue-field arithmetic, including
   IsFractionRing.stabilizerHom_surjective; no exact statement.
3. msearch.py loogle, query: `IntermediateField.fixedField, IsGalois, Sylow`.
   Result: 0 hits; no combined theorem with these inputs.
4. msearch.py grep, query: `IsAdmissibleFiniteSchemeQuotient|semilinear.*[Ss]ylow|[Ss]ylow.*quotient`,
   subdirectory AlgebraicGeometry. Result: 0 Mathlib hits.
5. rg on lean/WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry for
   geometric/categorical quotient declarations and IsAdmissibleFiniteSchemeQuotient.
   Found the existing Q112 definition used here and FSLogGroupAction.IsQuotient, whose
   fs-log data makes it a different notion. No theorem for the item.
6. rg and grep -rn for the exact item id and semilinear_sylow_good_components in the
   upstream and Sheaf algebraic-geometry trees: no declaration; only the mention in
   GabberGlobalSNCAlteration's proof docstring. No duplicate theorem was written.

Validation: every delivered Lean file (one) was compiled using the prescribed scompile.py
wrapper. The first compile found only overlapping IsProper/LocallyOfFiniteType instance
binders; redundant finite-type binders were removed, since properness already supplies
both locally-finite-type and quasi-compactness. The next compile was completely clean
in both sandbox and library modes (3.6 s and 3.4 s). No local lake or global build ran.

## Second reading by NI

Separate second pass in this worker session; the dispatcher explicitly forbids starting
other agents. Reopened the live JSON, the full generated Lean signature, the imported
quotient definition and the ILO source passage. This is a clause-by-clause reading, not
an assertion of a second person's review.

1. Return H1 is repaired by delivering one actual Lean module, its complete lean record,
   and both report sections. The declaration's proof is exactly sorry; the signature in
   lean.statement is copied verbatim from the file.
2. Return H2 is repaired by reconstructing the node from the live file. No proof,
   proof_deps, proof_origin, mathlib_searches or split_report change is delivered.
   Only the allowed lean record and the landed quotient-definition dependency are added.
3. The dropped quotient-existence result is absent from the node and module. The proof
   docstring follows the current finite-normal ample-descent route, not the superseded
   projective-quotient route. No existence theorem for arbitrary projective quotients is
   used as a statement assumption.
4. Rechecked fields, finite extension, prime/characteristic, normal proper B, finite
   disjoint integral cover, smooth projective Y, semilinear action, invariant projective
   surjection, and finite generic residues against the hypothesis table above. The
   nonfaithful-action case is preserved by using ρ.range and L.map ρ.
5. Checked quotient conditions individually. The imported predicate has invariant
   structure sheaf and finite quotient data; hcat and hgeom explicitly supply the two
   conditions absent from its declaration. Affine orbit neighbourhoods and quotient
   topology introduce no restriction because they follow from finite geometric quotient
   data. The maps d are forced, by uniqueness, from h and q.
6. Rechecked the dense open on d top, F fixed-field equation, Sylow order/index convention,
   constants degree, finite Galois clause, and equality of the image with fixingSubgroup.
   This does not accidentally demand that L act faithfully or that the original constants
   extension K/e be Galois.
7. Rechecked Qcirc's actual component union, clopenness, generic-fibre meeting, normality,
   projectivity over the actual F, and projective surjectivity to B. The residue-field
   finiteness and coprimality clauses are inside the quantifier over EVERY generic point
   of U.toScheme, so no total-degree weakening is present.
8. Rechecked Ycirc is literally q L inverse-image U, and the restricted quotient is
   literally resLE of q L. The quantified action aU is pinned by its commuting inclusion
   equation, and the same restricted map has finite/invariant/sheaf, categorical and
   geometric clauses. No arbitrary map or mere Nonempty replacement is used.
9. The only change found in this second pass was the redundant proper/finite-type
   instance warning, already removed and recompiled cleanly. No mathematical mismatch
   remains, and no statement correction is requested.
