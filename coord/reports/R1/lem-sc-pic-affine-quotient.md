## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient` states
`AlgebraicGeometry.IsConnectedCurve.pic_affine_quotient`, with one sorry and no definitions.
It is the universal, specified-boundary-subgroup version of the quotient presentation.
The existing upstream `IsConnectedCurve.exists_addEquiv_pic_quotient` only asserts existence
of a compactification and an unspecified finitely generated subgroup, so is not the same statement.

Hypothesis and clause correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Smooth affine connected curve C/k: `f : C ⟶ Spec (.of k)` with `[IsConnectedCurve f]`,
  `[Smooth f]`, and `[IsAffine C]`. The recorded connected-curve class includes separatedness,
  finite type, nonemptiness, connectedness, and dimension exactly one.
- Chosen smooth proper connected compactification and open immersion: `c : Compactification f`
  supplies `c.Z`, the structure map `c.g`, the open immersion `c.i`, its compatibility with f,
  and properness of `c.g`. `[IsConnectedCurve c.g] [Smooth c.g]` give the stated ambient curve.
- The source point-class construction requires relative dimension one:
  `[hsm : SmoothOfRelativeDimension 1 c.g]`. This is redundant mathematical data, equivalent to
  smoothness here, since `smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.g 1` and
  `IsConnectedCurve.krullDim_eq_one` give it. It excludes no smooth connected curve in the node.
- `[GeometricallyIntegral c.g]` is the prerequisite of the recorded `IsJacobian` definition.
  It is automatic for a smooth connected curve over an algebraically closed field: smoothness
  gives regularity and reducedness, connected regular locally Noetherian curves are irreducible,
  and integrality over an algebraically closed field is geometric integrality. It excludes no
  curve in the node and is not an independent mathematical restriction.
- Boundary S is the actual complement `(Set.range c.i.base)ᶜ`. Its finiteness is `hfin` and its
  being a set of closed points is `hcl` (singleton closedness for every boundary point).
- Chosen Jacobian: `J : Over (Spec (.of k))`, `[CommGrpObj J]`, `[IsJacobian c.g J]`.
  The recorded `IsJacobian` supplies abelian-variety structure, genus dimension, and the
  group-compatible representing isomorphism. Commutativity is the abelian-variety group law.
- Given identification of Pic⁰ with J(k): `G : Subgroup c.Z.Pic`, `hG` identifies its underlying
  set with `c.g.picZero`, and `e : G ≃* (𝟙_ (Over (Spec (.of k))) ⟶ J)` is the identification.
  No new degree-zero group is defined. The assertion holds for any such identification, hence
  for the given canonical one; changing the identification transports the subgroup and quotient.
- Boundary nonemptiness: `(Set.range c.i.base)ᶜ.Nonempty`, the first conjunct.
- Every P₀ in S: `∀ (P₀ : closedPoints c.Z), P₀.val ∉ Set.range c.i.base → ...`.
  Together with hcl this ranges over exactly all the boundary points.
- Lambda: `AddSubgroup.closure {a | ∃ (P : closedPoints c.Z) (L : G), ...}`. The first conjunct
  restricts P to S; the second makes `L.val` exactly `Pic.ofClosedPoint k P /
  Pic.ofClosedPoint k P₀`, i.e. [P] minus [P₀] in the multiplicative notation for Pic; the
  last transports that difference to `a = Additive.ofMul (e L)` in J(k). The degree-zero
  membership proof is expressed by the existential `L : G`, not a new theorem or a sorry in data.
  Every difference has degree zero since each closed point has degree one over k.
- Group isomorphism Pic(C) ≅ J(k)/Lambda: `Nonempty (Additive C.Pic ≃+ ... ⧸ ...)`.
  `Additive` only changes notation for the existing groups; existence, not a chosen map or
  a naturality condition, is precisely the node's conclusion.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`,
  `AlgebraicGeometry.IsConnectedCurve`, and `Scheme.Hom.picZero` (def-sc-curves).
  The general curve declaration alone does not mean connected curve; the same source module's
  recorded connected specialization gives exactly the required notion.
- `WeilConjectures.AlgebraicGeometry.Curve.Compactification`:
  `AlgebraicGeometry.IsConnectedCurve.exists_smooth_properCompactification`
  (lem-sc-compactification); its ambient connectedness, smoothness, finite complement and
  closed-boundary signatures specify exactly the data bound in this universal statement.
  This is a theorem about every chosen compactification satisfying those properties, so it does
  not invoke the existential compactification theorem as a term.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`:
  `AlgebraicGeometry.IsJacobian` (def-sc-jacobian), used directly.
- `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`:
  `AlgebraicGeometry.exists_jacobian`, `exists_picardZero_equiv_picardFunctorDegree_zero`, and
  `exists_mulEquiv_of_isPicardZeroMul` (thm-sc-jacobian-representability); the given group
  identification is the one their signatures provide. This universal statement binds that data.
- Source `WeilConjectures.AlgebraicGeometry.Curve.Picard`:
  `AlgebraicGeometry.Scheme.Pic.ofClosedPoint`, read with its docstring and full prerequisites;
  reused to express the point classes, not redefined. All these modules are reached by the
  two source imports. Mathlib's quotient-group import supplies the additive quotient.

Edge cases checked: C cannot be empty or zero-dimensional by IsConnectedCurve. An empty
boundary is contradicted by the first conjunct, for the proper-affine dimension reason in the
node proof. For A¹ compactified by P¹ the boundary is one point, all differences are zero,
and both Pic(A¹) and J(k) are trivial. A singleton boundary always gives the zero subgroup.
Genus zero, positive genus, all characteristics (including zero), and every finite cardinality
of the boundary are included. P = P₀ is a zero generator; no inequality is imposed. All
schemes and the field share the universe of the original source declarations.

Searches performed with msearch.py (recorded in searches.jsonl):

- LeanFinder: `Picard group of smooth affine curve quotient of Jacobian by boundary divisor
  differences`: eight hits concerning Weierstrass curves and class groups, none matching.
- Loogle: `AddSubgroup.closure, Additive`: two closure-transport lemmas; no curve quotient theorem.
- Mathlib grep: `Pic.*quotient|Jacobian|divisorClassGroup` in AlgebraicGeometry: eighteen hits,
  all concerning elliptic-curve Jacobian coordinates, no match.
- LeanSearch: `Picard group smooth affine curve quotient Jacobian boundary points`: unavailable
  (Internal Server Error); this failure was recorded and the other search kinds were used.
- rg of source AlgebraicGeometry and project lean/Sheaf for divisor/Picard, closed-point classes,
  Jacobian identification and boundary quotient: found the upstream existential quotient and
  the project's `Scheme.Hom.pic_restriction_boundary`, whose target is the degree-zero Picard
  subgroup rather than the Jacobian and whose conclusion includes restriction compatibility.
  Neither states this node. Found and reused the actual point-class definition.
- rg of upstream names, Mathlib, source and project for `PicAffineQuotient|pic_affine_quotient`:
  no conflicting declaration. Source search for the node id found no declaration.

Source read: Affine.lean's quotient presentation docstring and signature, including its
step-by-step boundary and degree-splitting proof, which the node source explicitly names.
The blueprint file is not present in this read-only clone; a direct fetch of its recorded
commit/path returned HTTP 404. The complete corresponding source proof is available in the
upstream Lean docstring, and all four node proof steps are transcribed in the new docstring.

Server compile: clean (no errors or warnings), 3.1 seconds. No statement correction, new node,
or dependency replacement was needed. The original node is changed only in its lean record.

## Second reading by R1

I independently opened the sandbox node and module, all four statement-dependency JSON
files, and the actual declarations in Curve.lean, Curve/Compactification.lean,
Curve/Picard.lean, AbelianVariety/Jacobian.lean and Picard/Jacobian.lean. I read the
source place explicitly recorded in the node: Curve/Affine.lean, the docstring and
signature of IsConnectedCurve.exists_addEquiv_pic_quotient (lines 233–255). This is
not a Stacks-tag node. The blueprint tree is absent here; the named Lean source place
supplies the boundary-divisor and degree-splitting argument. Its existential theorem
is weaker than this node's universal, specified-subgroup formulation and cannot be
recorded as an existing exact match.

The node's objects, hypotheses and conclusion, matched independently with the file:

1. An algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
   Verdict: exact, including positive characteristic.
2. A smooth affine connected curve C over k: `{C : Scheme.{u}}`, structure map `f`,
   `[IsConnectedCurve f] [Smooth f] [IsAffine C]`. The actual IsConnectedCurve class
   extends IsCurve (separated, locally finite type, quasi-compact, dimension at most
   one) and adds connectedness and dimension exactly one. Connectedness includes
   nonemptiness. Verdict: the required connected specialization, not merely IsCurve.
3. A chosen smooth proper connected curve C-bar and open immersion over k:
   `c : Compactification f`, `[IsConnectedCurve c.g] [Smooth c.g]`. I also opened
   Compactification/Defs.lean: `c.Z`, `c.g`, `c.i`, `c.comm`, `c.isProper`, and
   `c.isOpenImmersion` give precisely these objects and their compatibility.
   Compactification does not secretly impose density, projectivity or a choice of
   completion. Nonempty C is a dense open of the smooth connected integral ambient
   curve. Verdict: all and only the stated geometric data.
4. The finite closed boundary S: `S = (Set.range c.i.base)ᶜ`, `hfin : S.Finite`,
   and `hcl : ∀ x ∈ S, IsClosed ({x} : Set c.Z)`. Verdict: the actual complement,
   with both finiteness and closedness explicitly present, no extra points.
5. The point classes require `[hsm : SmoothOfRelativeDimension 1 c.g]`.
   I read the signature of smoothOfRelativeDimension_iff_topologicalKrullDim_eq:
   for a smooth scheme over a field with irreducible source it equates this with
   dimension one. Here irreducibility follows from smoothness, local
   Noetherianity and connectedness, as in the source compactification proof. Thus this is a
   redundant consequence, not a restriction on the node's curves. The extra
   `[GeometricallyIntegral c.g]` is required to type the recorded IsJacobian class.
   Smoothness gives regularity and reducedness; finite type gives local
   Noetherianity; connected regular locally Noetherian schemes are irreducible.
   Consequently c.Z is integral, and an integral finite-type scheme over an
   algebraically closed field is geometrically integral. Verdict: neither binder
   excludes an allowed case; neither is a vacuous replacement for a hypothesis.
6. A Jacobian J of C-bar: `J : Over (Spec (.of k))`, `[CommGrpObj J]`,
   `[IsJacobian c.g J]`. The actual IsJacobian declaration extends IsAbelianVariety,
   fixes dimension to genus, and supplies a group-compatible representing
   isomorphism of the degree-zero relative Picard functor. Verdict: the dependency's
   notion, not an arbitrary abelian group or an arbitrary abelian variety.
7. The identification Pic-zero(C-bar) with J(k): `G : Subgroup c.Z.Pic`,
   `hG : (G : Set c.Z.Pic) = c.g.picZero`,
   `e : G ≃* (𝟙_ (Over (Spec (.of k))) ⟶ J)`.
   I read picZero (degree zero), picardZero (the degree-homomorphism kernel),
   coe_ker_picDegreeHom and the representability-to-points comparison signatures.
   G is therefore exactly the recorded degree-zero subgroup, not a private notion.
   The terminal Over object is Spec k over itself, so these morphisms are J(k).
   IsJacobian is Prop and does not fix a particular representing isomorphism;
   the chosen canonical identification can be supplied as e. Quantifying over e
   does not change the quotient-existence assertion: if e₀ is the canonical one,
   `e ∘ e₀⁻¹` is a group automorphism of J(k) carrying the subgroup generated using
   e₀ to the subgroup generated using e, and hence induces an isomorphism of
   their quotients. Conversely the universal assertion applies to e₀.
   Verdict: equivalent formulation of the node's chosen identification, with no
   additional naturality or restriction-compatibility conclusion.
8. S is nonempty: `S.Nonempty`, the first conjunct. Verdict: explicitly present;
   the statement does not assume this conclusion.
9. Every P₀ in S: `∀ (P₀ : closedPoints c.Z), P₀.val ∉ Set.range c.i.base → ...`.
   Since hcl says every boundary point is closed, this ranges over exactly S.
   Verdict: the required universal quantifier, after the compactification is fixed.
10. Lambda is generated by all `[P] - [P₀]` in J(k): `AddSubgroup.closure` of
    the set with witnesses `P : closedPoints c.Z` and `L : G`, boundary membership,
    `L.val = Pic.ofClosedPoint ... P / Pic.ofClosedPoint ... P₀`, and
    `a = Additive.ofMul (e L)`. I read ofClosedPoint: it is the Picard class of the
    dual of the point ideal, hence O(P), not O(-P). The division is subtraction
    under Additive. Each difference has degree zero by the actual
    picDegreeHom_ofClosedPoint theorem (degree one over an algebraically closed
    field), so the witness L omits no generator. Verdict: exactly Lambda, not an
    unspecified finitely generated subgroup or its divisible saturation.
11. A group isomorphism Pic(C) with J(k)/Lambda:
    `Nonempty (Additive C.Pic ≃+ Additive (...) ⧸ AddSubgroup.closure ...)`.
    Verdict: existence of the required group isomorphism, with no stronger
    compatibility clause. Additive changes notation only.

Edge cases: empty C and a zero-dimensional C are excluded by the node's definition
of connected curve and equally by IsConnectedCurve. Empty S is not silently
excluded by a binder; its impossibility is the first conclusion (proper affine
finite would force dimension zero). For a one-point boundary, P = P₀ is allowed,
the point quotient is the identity and Lambda is zero. For A¹ in P¹ this gives the
trivial Picard group and genus-zero Jacobian. Genus zero and positive genus, all
finite boundary cardinalities and all characteristics remain covered. There is no
n binder or characteristic restriction. Universe u is bound, as are every object
and variable; Scheme, the field and Over use the source declarations' common
universe. There is no quantification over test objects in a smaller universe.

Independent searches, using wording different from the first worker:

- LeanFinder via msearch: `restriction of line bundles to an open smooth curve
  kernel generated by missing points`. Eight hits about stalks, restriction of
  ideal sheaves, vector-bundle trivializations and differentials; no exact match.
- Loogle via msearch: `AddSubgroup.closure, QuotientAddGroup`. No hits; the latter
  identifier was unrecognized. This is recorded as an unsuccessful query, not
  evidence that the curve theorem is absent.
- Mathlib grep via msearch in AlgebraicGeometry:
  `pic.*restrict|pic.*quotient|boundary.*divisor`. No hits.
- LeanSearch via msearch: `Picard group of an open curve modulo classes of omitted
  closed points`. Service returned Internal Server Error, recorded unavailable.
- Independent rg on source WeilConjectures/AlgebraicGeometry and project
  lean/Sheaf/AlgebraicGeometry for `pic.*quotient|boundary.*(pic|divisor)|
  pic.*restriction|point.*difference` found the upstream existential quotient,
  the project PicRestrictionBoundary statement, and unrelated torsor quotients.
  I opened PicRestrictionBoundary. It gives a quotient of the degree-zero Picard
  subgroup with restriction compatibility, not this Jacobian quotient assertion;
  it does not warrant dropping this module as an existing exact match.

No new definition nodes or dependency modules are in this delivery. The actual
recorded dependencies supply the notions needed here; there is no missing notion,
private copy, hollow definition or data sorry. The module contains one theorem
with proof `sorry`, and no proved result. Its docstring includes the source place,
blueprint id and all four node proof steps, including the explicit retraction by
P₀ rather than an unspecified degree splitting. Imports are used, all lines fit
the 100-character convention, and the namespace is the upstream namespace.
The lean.statement record agrees verbatim with the theorem signature.

Mismatches found: none requiring repair. I left the correct Lean and node unchanged
and appended this independent review only. Server scompile was clean in 2.5 seconds,
with exit code 0 and no warnings. No statement correction or disputed flag is needed.
