## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveHypersurfaceStructureSequence` states
`AlgebraicGeometry.Proj.projective_hypersurface_structure_sequence`, with one
postponed proof (`sorry`). It preserves the node statement and all dependency
lists. There are no new DAG nodes, dependency repairs or statement corrections.

The two supporting declarations belong to the same notion. The instance
`hypersurfacePolynomialGrading` is transparently Mathlib's
`MvPolynomial.gradedAlgebra`, exposing the existing total-degree grading without
using a file-local instance or assuming an extra grading. The real definition
`hypersurfaceMultiplication` composes `Proj.twistMul (-d) hF`, the equality
`-d+d=0`, and `Proj.unitIsoTwistZero.inv`. It therefore constructs exactly the
canonical multiplication O(-d) -> O, with no existentially chosen map. Neither
supporting declaration contains a postponed proof or data.

Hypothesis and clause correspondence, using S for the written-out type
`MvPolynomial (Fin (n + 1)) k`, A for its written-out homogeneous submodules,
and i for `Proj.map q (GradedRingHom.irrelevant_le_map_of_surjective hq)`:

- Field k: `{k : Type u} [Field k]`, with arbitrary explicit universe u.
- n >= 1 and d >= 1: `(n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d)`.
- S=k[x_0,...,x_n], variables of degree one: the literal MvPolynomial type
  and `MvPolynomial.homogeneousSubmodule`; the global supporting instance is
  the prescribed `MvPolynomial.gradedAlgebra` data, rather than another grading.
- Nonzero homogeneous equation: `(F : S) (hF : F.IsHomogeneous d) (hF0 : F ≠ 0)`.
- P=Proj(S): `Proj A` throughout. On this Proj the standard twist is the
  recorded `Proj.twist A (-d)`, not a module on a second projective-space model.
- Z=Proj(S/(F)): the existential grading `ℬ` is on the literal ring
  `S ⧸ Ideal.span {F}`. Its components are explicitly the images of A_e under
  `Ideal.Quotient.mk`. Thus the conclusion supplies the quotient grading,
  rather than requiring the caller to assume its existence. The GradedRing
  witness is only used while stating the conclusion; no definition chooses
  unspecified data from the postponed theorem.
- Canonical closed immersion with quotient subscheme structure: the graded map
  `q : A →+*ᵍ ℬ` is surjective and is constrained on every a by
  `q a = Ideal.Quotient.mk (Ideal.span {F}) a`. The immersion is the existing
  canonical `Proj.map q ...`, and `IsClosedImmersion i` is asserted. Thus no
  arbitrary morphism or replacement closed subset is supplied as a hypothesis.
- O(-d): the standard recorded `Proj.twist A (-(d : ℤ))`.
- O: `Scheme.Modules.unit (Proj A)`.
- i_*O_Z: the target of `SheafOfModules.unitToPushforwardObjUnit
  i.toRingCatSheafHom`, definitionally `Scheme.Modules.pushforward i` applied
  to `Scheme.Modules.unit (Proj ℬ)`.
- First displayed arrow: the constructed `hypersurfaceMultiplication hF`.
- Final arrow r: the actual `SheafOfModules.unitToPushforwardObjUnit` attached
  to the scheme morphism's own structure-sheaf homomorphism. It is neither an
  arbitrary map satisfying exactness nor a separately chosen quotient arrow.
- Short exactness: `∃ hz : multiplication ≫ r = 0,
  (ShortComplex.mk multiplication r hz).ShortExact`. Its zero composite,
  monomorphism, exactness, and epimorphism give precisely the two zero-ended
  short exact sequence in the node.
- O=tilde S: `Proj.basicOpenIsoAway A g hg he` is the existing canonical chart
  ring isomorphism used to interpret the multiplication formula. It also
  supplies the scalar action for both associated-sheaf identifications.
- O(-d)=tilde S(-d): `alpha g e he hg` is an injective additive map into the
  ordinary localization of S at g, with range exactly the fractions a/g^m
  for homogeneous a of degree r and `r = m*e-d` in ℤ. This is exactly degree
  zero for S(-d), or equivalently degree -d in S_g. The scalar formula says
  alpha(c*s)=c*alpha(s). Thus its bijection to this range is a module
  identification; no independent associated-sheaf construction is introduced.
- Multiplication is the sheafification of a -> F*a: in the canonical O chart,
  its value is `alpha(s) * algebraMap S (Localization.Away g) F`. By
  commutativity this is F*a/g^m on every homogeneous fraction.
- Coordinate chart generator: for every `j : Fin (n+1)`, the specified
  `Proj.twistPowSection (-d) (MvPolynomial.isHomogeneous_X k j)` is sent to
  `Proj.awayToSection ... (Away.mk ... d F ...)`, exactly X_j^(-d) -> F/X_j^d.
- i_*O_Z=tilde(S/(F)): `beta g e he hg` is a ring equivalence from the actual
  Z structure sheaf on `i ⁻¹ᵁ D_+(g)` to `HomogeneousLocalization.Away ℬ (q g)`.
  The latter is the degree-zero part of (S/(F)) localized at q(g), or of the
  quotient S-module localized at g. The scalar formula is compatibility with
  the quotient-localization ring map `Away.map q g`, so the ring equivalence
  is also the required O_P(D_+(g))-linear identification. The underlying
  additive group here is definitionally the section of the module pushforward.
- Quotient arrow on every positive homogeneous basic open: for every e>0,
  homogeneous g of degree e, m and homogeneous a of degree m*e, beta sends
  `i.app D_+(g) (awayToSection ... (Away.mk ... m a ha))` to
  `Away.mk ℬ (q.map_mem hg) m (q a) (q.map_mem ha)`. This is exactly
  a/g^m -> q(a)/q(g)^m for the actual structure-sheaf map, under beta.
- All restriction compatibilities: alpha and beta each have a formula for
  every inclusion D_+(h) <= D_+(g), every t>0 and equation h^t=b*g, and
  every fraction representative a/g^m or c/q(g)^m. After the actual sheaf
  restriction, the numerator is b^m*a or q(b)^m*c and the denominator is
  h^(t*m) or q(h)^(t*m), respectively. This is the canonical localization
  restriction in both identifications, including all choices of representatives.
- The ideal remains exactly `(F)` via `Ideal.span {F}` everywhere. No
  radical, reduced structure, integrality of Z, irreducibility, smoothness,
  algebraic closure of k or characteristic restriction is imposed.

The local identifications render all the associated-sheaf assertions without
needing a private definition of tilde for graded modules. In particular,
`Proj.twist` is the recorded O(-d) itself, and alpha supplies its stated shifted
module chart identification. Beta is into the actual homogeneous quotient-ring
localization, not a cokernel sheaf with an unspecified identification to Z.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`; available through the polynomial imports.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, with its total-degree
  components and existing grading from `Mathlib.RingTheory.MvPolynomial.Homogeneous`.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme` and `.Basic`:
  `AlgebraicGeometry.Proj`, `projIsoSpec`, `Proj.basicOpen`, `Proj.awayToSection`,
  and `Proj.basicOpenIsoAway`; the underlying basic opens are
  `ProjectiveSpectrum.basicOpen` from `.Topology`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent arbitrary-site alias of `SheafOfModules`. Scheme modules
  used here are that same Mathlib category specialized to the scheme ringed site.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`:
  `Proj.twist`, `Proj.twistMul`, `Proj.unitIsoTwistZero`;
  `.UnitToTwist`: `Proj.unitToTwist`; `.TensorObj`: `Proj.twistPowSection`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `ProjectiveSpace.twist` and its transition interpretation, imported for the
  proof plan. Its distinct base-change projective-space model is not confused
  with the concrete polynomial Proj appearing in this node. The recorded Proj
  twist is the one used by the recorded polynomial chart theorem as well.
- `Sheaf.AlgebraicGeometry.ProjGradedSheafificationExact`:
  `Proj.graded_sheafification_shortExact` (proof dependency).
- `WeilConjectures.AlgebraicGeometry.ProjTildeFunctorial`:
  `Proj.tilde_functorial` (proof dependency).
- `WeilConjectures.AlgebraicGeometry.ProjPolynomialTwistChart`:
  `proj_polynomial_twist_chart` (proof dependency).
- `Sheaf.AlgebraicGeometry.GradedProjQuotientTwistComparison`:
  `Proj.gradedQuotientTwistComparison` (proof dependency).
- `WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists`:
  `Proj.gradedModuleSheaf_exists` (proof dependency).
- `WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties`:
  `Proj.standardOpenProperties` (proof dependency).
- `Mathlib.Topology.Sheaves.SheafCondition.Sites`:
  `TopCat.Sheaf.restrictHomEquivHom`, `extend_hom_app`, `hom_ext`, and
  `isIso_iff_isIso_basis` (proof dependency's Mathlib matches).

All stated proof dependencies are imported with plain import; dependencies
needed for the signature are public imports. The theorem docstring carries all
six proof steps, including how the quotient charts are identified and why the
formulas glue. The node's statement and metadata are unchanged except for `lean`.

Edge cases checked mathematically before finalizing:

- n=1 and d=1 are included. n=0 and d=0 are excluded only because the node
  explicitly excludes them, not to satisfy a library interface.
- Repeated factors F=X_0^d, d>1: the quotient retains nilpotents; no radical
  enters either the ring, the scheme or the formula. On D_+(X_0) the quotient
  localization can be zero, as required by the empty hypersurface chart there.
- g=0 is allowed as a homogeneous polynomial of every positive degree. Both
  structure-sheaf sections over its empty basic open and its localization are
  the zero ring; alpha's range contains zero by choosing m sufficiently large.
- More generally q(g) nilpotent: the target standard open is empty and its
  homogeneous localization is the zero ring. No Nontrivial instance is required
  on the quotient or its localizations. Beta is still a valid ring equivalence.
- Arbitrary positive characteristic, reducible or singular F, finite fields,
  and arbitrary coefficient universe u are all retained.
- The quotient grading and q are conclusions with their full prescribed data,
  not additional hypotheses. In particular the theorem does not assume the
  exact sequence, its maps, its comparison isomorphisms or chart formulas.
- The beta scalar law is expressed using multiplication by the actual image
  under i.app, avoiding any assumption of an unrelated module structure on Z.

Searches performed on 2026-10-24 (the wrapper's exact queries/results are also
in sandbox searches.jsonl):

- LeanFinder through msearch.py: "A nonzero homogeneous polynomial defines a
  short exact sequence from O(-d) to O to the pushforward of its projective
  hypersurface structure sheaf". Eight hits, including Proj.awayι,
  Proj.fromOfGlobalSections and Proj.awayToSection, give Proj chart constructions,
  not the required exact sequence.
- Loogle through msearch.py: `"Proj", "Exact"`. Twelve hits about abstract
  projective objects and short complexes, including
  `CategoryTheory.ShortComplex.Exact.liftFromProjective`; no hypersurface result.
- Mathlib grep through msearch.py in AlgebraicGeometry:
  `hypersurface.*exact|exact.*hypersurface|twist.*shortExact`: zero hits.
- LeanSearch through msearch.py: "A nonzero homogeneous polynomial defines the
  short exact structure sheaf sequence of a projective hypersurface". Eight
  hits, all Proj structure-sheaf constructions and chart identifications,
  including `Proj.basicOpenIsoAway`; no exact hypersurface statement.
- rg over `lean/WeilConjectures` and `lean/Sheaf` for hypersurface names,
  the item id, and the proposed declaration names, plus the prescribed
  `grep -rn` for the item id in WeilConjectures. No item declaration or name
  clash exists. `PlaneHypersurfaceCohomology` describes the plane case in its
  proof docstring but its theorem states cohomology, not this sequence.
  `ProjLineCoordinateShortExact` treats the two-coordinate sequence, not this
  quotient by an arbitrary homogeneous equation.
- Read the node's full proof and all statement-dependency records, and the
  exact recorded Proj twist, projective-space twist and general ringed-site
  module declarations and docstrings. The source curves.tex around
  lemma-genus-plane-curve contains the two displayed sequences. No newer
  blueprint node with this exact item id occurs in literature/blueprint/latest.

Validation: scompile.py Q101 lem-sfb-projective-hypersurface-structure-sequence
compiled the module in sandbox and library mode cleanly (9.3 and 12.9 seconds).
The initial elaboration identified parenthesization and scalar-action issues;
these were repaired using the actual scheme structure map. No declaration probe
or extra diagnostic command remains in the delivered file. Dry-run deliver2.py --no-push passed server preflight and compilation
(commit 2c3146bd430); delivery runs the same checks again before pushing.

No STATEMENT-DISPUTED condition or node fault remains.

## Second reading by Q101

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
