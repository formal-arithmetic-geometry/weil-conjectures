# H5: proper/open transport adjunct bridge

The assigned theorem's exact signature and public import are preserved. Its proof
now imports the new forward-lambda support theorem and uses adjunction uniqueness,
the existing intrinsic gamma-adjunct equation, and inverse cancellation. Local
proof attributes name existing definitions as irreducible only during elaboration;
there is no public attribute or instance change.

The five support modules are new under Sheaf. They construct the actual factor
diagram, state three strictly smaller remaining factor/component equations, and
prove the forward bridge by categorical pasting. No adopted source-library module
is changed. Related importers are checked by delivery.
