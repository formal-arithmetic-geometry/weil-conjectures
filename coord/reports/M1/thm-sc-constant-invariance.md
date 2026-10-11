## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` states
`AlgebraicGeometry.IsConnectedCurve.constant_cohomology_baseChange_compatible`.
Its only proof is `sorry`; it defines no new notion. The node is unchanged except for `lean`.
The blueprint node and the whole unit were read from the project server (the literature
files are absent in this machine's read-only clone). The unit record
`dag/units/sk-prop-ext-invariance.json` was also read locally.

Hypotheses and objects:

- Algebraically closed extension k ⊆ K: explicit `{k K : Type u}`, `Field`, `IsAlgClosed`,
  and `Algebra k K`. The field algebra map is injective automatically.
- Smooth separated connected curve: `f : C ⟶ Spec (.of k)`, `[IsConnectedCurve f]`,
  `[Smooth f]`. The recorded class extends `IsCurve`, whose fields include separatedness,
  finite type and dimension at most one. `IsConnectedCurve` supplies nonempty connectedness
  and dimension exactly one; no arbitrary zero-dimensional point is admitted.
- Chosen smooth proper connected compactification: `c : Compactification f`,
  `[IsConnectedCurve c.g]`, `[Smooth c.g]`, `_hfin` and `_hclosed` give precisely the
  finite set of closed boundary points. Properness and the open immersion are fields of
  `Compactification`; no density hypothesis is added. The nonempty open curve is dense in
  the smooth connected compactification. If C is proper its embedding is an isomorphism.
- g = genus of the compactification: every coordinate product uses `c.g.genus`.
  There is no independent genus parameter or extra genus equality assumption.
- n ≥ 1 prime to char k: `(n : ℕ) [NeZero n] (_hn : (n : k) ≠ 0)`.
  For natural n, `NeZero n` says n ≥ 1; field nonvanishing says the characteristic
  does not divide n, equivalent to prime-to-characteristic. No primality of n is assumed.
  `NeZero n` is derivable already from field nonvanishing but is explicitly bound for the
  existing roots-of-unity trivialization, not an extra restriction.
- C_K and its projection are Mathlib's `pullback`, `pullback.snd`, `pullback.fst` for
  `f` and `Spec.map (CommRingCat.ofHom (algebraMap k K))`, exactly def-sc-field-extension.

Conclusions and compatibility:

- The witness `r` is uniquely constrained, in every degree, to be `Etale.cohomologyMap`
  followed by `Sheaf.H.map` of `Scheme.upperStarConstantSheafIso`. This is the canonical
  pullback into the coefficient sheaf on C_K, not an arbitrary isomorphism between groups.
  `∀ q : ℕ, Function.Bijective (r q)` states the isomorphism for every q ≥ 0. The comparison
  is an isomorphism, so this is equivalent to bijectivity of the node's original rho into
  the inverse-image sheaf of def-sc-field-extension.
- `C.constantZMod n` is the recorded source definition of constant Z/n coefficients.
  The blueprint writes F_n for this same cyclic sheaf (including composite n).
- For each primitive root ζ and its image (quantifying over all proofs that the image is
  primitive), `t`, `tK` are additive equivalences constrained to be `Sheaf.H.map` of the
  existing `constantZModIsoRootsOfUnitySheaf`. They are witnesses for defined maps,
  not new data or assumptions. The quantification is nonvacuous: primitive roots exist
  for every permitted n, and remain primitive under the injective field map.
- The equation involving `kernel.ι (n • 𝟙 C.gmSheaf)` is the canonical map
  H1(μ_n) → H1(G_m), identified with Pic by
  `Scheme.Pic.toCohomologicalPicardGroupAddEquiv`. It says that under t and tK the map
  r1 induces exactly `Scheme.Pic.map` on Picard n-torsion. This is the proper H1
  identification and the right edge of the affine short exact sequence.
- The `kummerδ₁` equation on every line bundle is the canonical Pic/n → H2(μ_n)
  identification commuting with r2. The invertibility proofs on both curves are universally
  quantified: no invertibility assumption is added to the theorem.
- In the proper case the genus after base change equals `c.g.genus`; the two H1 coordinate
  equivalences to `(Z/n)^(2g)` are required to match under r1. Bases are noncanonical in
  lem-sc-pic-proper-ntorsion, so this is simultaneous existence of compatible bases, not
  a claim that independently chosen bases agree. The preceding Picard equation fixes the
  underlying torsion pullback canonically.
- The two H2 equivalences to Z/n commute with r2 and are required, on every Picard class
  under the Kummer coboundary, to equal `picDegree` modulo n, on each curve separately.
  Thus arbitrary abstract H2 isomorphisms cannot satisfy this clause in place of the
  degree identification. It covers precisely the proper Picard cokernel identification.
- Jacobian compatibility is written in the recorded form of `genus_jacobian_invariant`,
  with every `let` expanded: for any representing group identifications e and eK,
  an isomorphism JK ≅ J_K matches their classifying maps on every degree-zero line bundle
  over every K-test scheme T. The equation is the whole final compatibility clause of
  that dependency, rather than merely asserting abstractly isomorphic Jacobians.
  It is stated both for C when proper and for the chosen proper compactification c.Z,
  whose Jacobian is the one used in the affine Picard presentation. Required geometric
  integrality, connected-curve and smoothness instances are existential conclusions,
  as in the recorded dependency, not added assumptions.
- In the affine case the `kummerδ₀` equation is the left edge of the short exact sequence:
  r1 matches the boundary of a unit with the boundary of its pullback by `Units.map π.appTop`.
  The equation with the Kummer inclusion above is its right edge.
- The last affine equation states that restriction of every degree-zero line bundle from
  c.Z to C commutes with field extension. The base-changed open immersion is the existing
  `pullback.map`; its coherence proofs are `Category.comp_id`, `Category.id_comp` and c.comm,
  with no postponed data. In the presentation of lem-sc-pic-affine the quotient map is
  precisely this restriction from Pic0(c.Z), identified with J_c.Z(k). This equation,
  together with the compactification's Jacobian square, says that the quotient
  identifications commute with the same Picard pullback induced by r1. It does not
  assert compatibility with an unrelated arbitrarily chosen quotient isomorphism.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`,
  `AlgebraicGeometry.IsConnectedCurve`, `AlgebraicGeometry.Scheme.Hom.genus`.
- `WeilConjectures.AlgebraicGeometry.Curve.Compactification`:
  `AlgebraicGeometry.IsConnectedCurve.exists_smooth_properCompactification` and its
  `Compactification` carrier, from `WeilConjectures.Compactification.Defs`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `AlgebraicGeometry.Etale.cohomologyMap`; `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`.
- `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion`:
  `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion` supplies the torsion/cokernel
  identifications referenced by the proper compatibility clauses and stage-3 proof.
- `Sheaf.AlgebraicGeometry.GenusInvariant`:
  `AlgebraicGeometry.genus_jacobian_invariant`; its recorded compatibility signature is
  expanded directly in the statement, using `IsJacobian`, `IsPicardZeroMul`,
  `picardFunctorDegree`, `picardSubfunctorDegree`, and `pullbackLeftPullbackSndIso`.
- `WeilConjectures.AlgebraicGeometry.Curve.Affine`:
  `AlgebraicGeometry.IsConnectedCurve.exists_addEquiv_pic_quotient` and
  `surjective_zsmul_pic_and_finite_torsionBy`. Their quotient interpretation is respected
  by the Picard restriction square, rather than a duplicate notion of Jacobian quotients.
- Other existing maps in the compatibility equations: `Scheme.constantZMod`,
  `Scheme.constantZModIsoRootsOfUnitySheaf`, `Scheme.kummerδ₀`, `Scheme.kummerδ₁`,
  `Scheme.Pic.toCohomologicalPicardGroupAddEquiv`, `Scheme.Pic.map`, and
  `Scheme.upperStarConstantSheafIso`, read in Sites.Kummer, Sites.RootsOfUnity,
  Sites.GmPicard, Picard.Group, and ConstructibleSheaf.Defs respectively.

Edge cases checked before writing: n = 1 gives zero cyclic coefficients and zero torsion,
so all statements remain valid; n = 0 is excluded exactly by the node's n ≥ 1 condition;
characteristic zero and positive characteristic are both covered by field nonvanishing;
composite n prime to the characteristic is allowed; genus zero uses `Fin 0`; q = 0 and
arbitrarily high degrees are quantified, including proper vanishing above two and affine
vanishing above one. Empty and zero-dimensional schemes are excluded only by the node's
connected-curve hypothesis. Identity field extensions give the same canonical maps.
All schemes, fields, and test schemes use an explicitly bound common universe u; this is
not an independently smaller test universe. No implicit variables or universes are used.

Searches (recorded by msearch.py in searches.jsonl):

- LeanSearch: “Etale cohomology of constant ZMod sheaves on smooth curves invariant under
  algebraically closed field extension”: service unavailable (Internal Server Error).
- Loogle: `Function.Bijective, ZMod`: two unrelated hits, `ZMod.castHom_bijective`
  and `bijective_rootsOfUnityAddChar`; neither is étale cohomology or compatibility.
- LeanFinder: “Etale cohomology constant sheaf of ZMod n smooth connected curve invariant
  under algebraically closed field extension compatibly with Picard torsion and degree”:
  eight unrelated hits (Hilbert 90 group cohomology, cotangent cohomology, class numbers).
- Mathlib grep: `cohomologyMap|constantZMod|constantModSheaf` in AlgebraicGeometry:
  zero hits.
- Source and Sheaf rg searches for cohomologyMap, constant invariance, and the item id
  found `AlgebraicGeometry.bijective_cohomologyMap_constantZMod` and its smooth-curve
  specialization in SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension.
  Both full signatures and docstrings were read: they supply bijectivity only, not
  Picard/degree/Jacobian compatibility, so they do not realize this whole node.
  Curve.FieldExtension and Curve.SmoothCalculations contain more general invariance
  results for torsion or module coefficients, also without these compatibility clauses.
  Existing Sheaf modules supply proper computations and the genus/Jacobian square, but
  no theorem bundles the requested statement. Searches of the source, Sheaf tree and
  dag/lean_names_upstream.json for the proposed full declaration name gave no clash.

No statement correction, disputed statement, new definition node, or dependency module.
The naturality equations make the blueprint's compatibility clause explicit without
changing its objects or choosing private copies of any dependency notion. The proof
sketch in the docstring follows all three steps of the reviewed node.

Validation: server single-file compile and the delivery dry run are run on this module;
the independent second reader will write the second-reading section and deliver.

## Second reading by M1

I independently read the node statement, its source place, the dependency records, and
`ConstantInvariance.lean` clause by clause. The object and hypothesis matching is as follows:

- The extension `k ⊆ K` is rendered by `{k K : Type u}`, `[Field k]`, `[Field K]`,
  `[IsAlgClosed k]`, `[IsAlgClosed K]`, and `[Algebra k K]`. The common universe does not
  remove any case covered by the node, and fields make the algebra map injective.
- The curve `C` over `k` is `(f : C ⟶ Spec (.of k))` with `[IsConnectedCurve f]` and
  `[Smooth f]`. The recorded `IsConnectedCurve`/`IsCurve` declaration supplies the
  separated finite-type one-dimensional curve conditions required by the node.
- The compactification is `c : Compactification f`, with connected and smooth instances;
  `_hfin` and `_hclosed` state that its open complement is finite and consists of closed
  points. Properness and open immersion are fields of `Compactification`, so no extra
  geometric object is introduced.
- The genus is exactly `c.g.genus`, the recorded `Scheme.Hom.genus` of the chosen
  compactification. The integer condition is `(n : ℕ) [NeZero n] (_hn : (n : k) ≠ 0)`,
  exactly `n ≥ 1` and prime to the characteristic, with composite `n` allowed.
- The base change and projection are exactly `pullback f (Spec.map (CommRingCat.ofHom
  (algebraMap k K)))`, `pullback.fst`, and `pullback.snd`, the objects in
  `def-sc-field-extension`.

The conclusion has every clause of the node. The existential `r` is the canonical
`Etale.cohomologyMap` followed by `Scheme.upperStarConstantSheafIso`, and
`∀ q, Function.Bijective (r q)` gives the isomorphism for every degree, including zero and
all higher degrees. For every primitive root and its primitive image, the witnesses `t` and
`tK` are constrained to the canonical roots-of-unity sheaf maps. The next equations spell
out the node's compatibility with the Kummer inclusion and with `Pic.map` on Picard
classes. The proper implication contains genus invariance, simultaneous compatible
`(Z/n)^(2g)` bases in degree one, and compatible degree identifications in degree two,
including the `picDegree` equations on both curves. Its following two blocks are the full
Jacobian compatibility of `lem-sc-genus-invariant`, once for `C` and once for `c.g`, with
all test schemes and degree-zero classes quantified. The affine implication contains the
Kummer unit boundary equation and the compactification Picard restriction square exactly
as the affine identification requires. Quantifiers occur in the same order as these
clauses, and no proof is supplied (`sorry` only).

I checked edge cases explicitly: `n = 1` is admitted and gives the zero cyclic coefficient
case; `n = 0` is excluded by `NeZero`; characteristic zero and positive characteristic are
covered subject to `_hn`; genus zero is represented by `Fin 0`; `q = 0` and arbitrary
higher degrees are quantified; identity field extensions are admitted; and the connected
curve hypotheses intentionally exclude empty and zero-dimensional schemes, as the node
requires. The shared universe is at least the field/scheme universe and introduces no
smaller test universe.

I repeated the duplicate searches with `rg` over the source and project trees and Mathlib,
and checked the existing source declarations
`AlgebraicGeometry.bijective_cohomologyMap_constantZMod` and
`AlgebraicGeometry.bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension`.
They prove only bijectivity of the basic cohomology map and do not state this node's
Picard, degree, genus, Jacobian, or affine compatibility bundle. LeanSearch was unavailable,
while Loogle/LeanFinder returned only unrelated `ZMod` and cohomology results; these are
recorded in `searches.jsonl`. The dependency declarations and modules were opened and used;
no missing notion, unusable dependency, or new definition node was found.

No semantic mismatch was found between the node and the Lean statement. I added only the
node's required `lean` record, containing the verbatim theorem signature, and this second
reading section. The module compiles cleanly with the required server single-file compiler.
