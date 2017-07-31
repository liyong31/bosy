import PackageDescription

let package = Package(
    name: "BoSy",
    targets: [
        Target(name: "BoSy", dependencies: ["Automata", "LTL", "Logic", "Utils"]),
        Target(name: "Automata", dependencies: ["Logic", "Utils"]),
        Target(name: "Logic", dependencies: ["Utils"]),
        Target(name: "LTL"),
        Target(name: "Utils"),
    ],
    dependencies: [
        .Package(url: "https://github.com/ltentrup/CAiger.git", majorVersion: 0, minor: 1),
    ]
)
