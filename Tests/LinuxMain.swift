import XCTest
@testable import BoSyTests
@testable import LTLTests
@testable import UtilsTests

XCTMain([
     testCase(BooleanTest.allTests),
     testCase(FunctionTest.allTests),
     testCase(GraphTest.allTests),
     testCase(LTLTests.allTests),
])